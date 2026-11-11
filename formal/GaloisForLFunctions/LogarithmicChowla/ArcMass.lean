import GaloisForLFunctions.LogarithmicChowla.DiscreteFourier
import GaloisForLFunctions.LogarithmicChowla.EntropyDecrement

/-!
# The mass of a major arc

`S_n(α) = Σ_{m<M} λ(n+m) e(mα)` (`lamSum`) and the twisted short mean square
`V(θ, T) = L(|T⁻¹ Σ_{u<T} λ(n+u) e(uθ)|²)` (`twistVar`). For the residues `r mod R` with `r/R`
within `1/(4T)` of `θ` modulo `1` (`arcSet`), and `R ≥ M + T`:

`R⁻¹ Σ_{r ∈ arc} L(|S_n(r/R)|²)/M ≤ 4V(θ, T)(M+1)/M + 8T/M` (`arc_mass_le`).

Gallagher's device in discrete form. With box sums `B_s = Σ_{u<T} a_{s+u} e((s+u)θ)` of the
sequence shifted by `T` (`box`), `Σ_s B_s e(sφ) = e(T(θ+φ)) S_n(θ+φ) D_T(φ)` (`sum_box_mul_ex`); on
the arc `|D_T(φ)| ≥ T/2`, and Parseval over `ℤ/R` bounds the arc by `4R/T² Σ_s |B_s|²`. A full box is
a shifted window, so `L(|B_s|²) = T² V(θ, T)`; at most `2T` boxes are partial, each `≤ T²`.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Complex Filter

noncomputable section

/-- `S_n(α) = Σ_{m<M} λ(n+m) e(mα)`. -/
def lamSum (n M : ℕ) (α : ℝ) : ℂ := ∑ m ∈ range M, (lam (n + m) : ℂ) * ex (m * α)

/-- `V(θ, T) = L(|T⁻¹ Σ_{u<T} λ(n+u) e(uθ)|²)`. -/
def twistVar (U : Ultrafilter ℝ) (θ : ℝ) (T : ℕ) : ℝ :=
  limAvg U (fun n => Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * θ)) / (T : ℝ) ^ 2)

theorem normSq_le_sq_of_norm_le {z : ℂ} {B : ℝ} (h : ‖z‖ ≤ B) : Complex.normSq z ≤ B ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg z) h 2

theorem norm_sum_lam_ex_le (n T : ℕ) (f : ℕ → ℕ) (φ : ℕ → ℝ) :
    ‖∑ u ∈ range T, (lam (f u) : ℂ) * ex (φ u)‖ ≤ T := by
  calc ‖∑ u ∈ range T, (lam (f u) : ℂ) * ex (φ u)‖
      ≤ ∑ u ∈ range T, ‖(lam (f u) : ℂ) * ex (φ u)‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ range T, (1 : ℝ) := by
        refine sum_le_sum fun u _ => ?_
        rw [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact abs_lam_le _
    _ = T := by simp

theorem norm_lamSum_le (n M : ℕ) (α : ℝ) : ‖lamSum n M α‖ ≤ M :=
  norm_sum_lam_ex_le n M (fun m => n + m) (fun m => m * α)

theorem bdd_normSq_lamSum (M : ℕ) (α : ℝ) : Bdd fun n => Complex.normSq (lamSum n M α) :=
  ⟨(M : ℝ) ^ 2, fun n => by
    rw [abs_of_nonneg (Complex.normSq_nonneg _)]
    exact normSq_le_sq_of_norm_le (norm_lamSum_le n M α)⟩

theorem lamSum_add_int (n M : ℕ) (α : ℝ) (j : ℤ) : lamSum n M (α + j) = lamSum n M α := by
  unfold lamSum
  refine sum_congr rfl fun m _ => ?_
  rw [show (m : ℝ) * (α + j) = m * α + ((m * j : ℤ) : ℝ) by push_cast; ring, ex_add_int]

/-- The sequence `λ(n + s − T)` on `T ≤ s < M + T`. -/
def shiftedLam (n M T s : ℕ) : ℂ := if T ≤ s ∧ s < M + T then (lam (n + (s - T)) : ℂ) else 0

/-- Box sums `B_s = Σ_{u<T} a_{s+u} e((s+u)θ)`. -/
def box (n M T : ℕ) (θ : ℝ) (s : ℕ) : ℂ :=
  ∑ u ∈ range T, shiftedLam n M T (s + u) * ex ((s + u : ℕ) * θ)

/-- **Box identity.** `Σ_{s<M+T} B_s e(sφ) = e(T(θ+φ)) S_n(θ+φ) D_T(φ)`. -/
theorem sum_box_mul_ex (n M T : ℕ) (θ φ : ℝ) :
    ∑ s ∈ range (M + T), box n M T θ s * ex (s * φ)
      = ex (T * (θ + φ)) * lamSum n M (θ + φ) * dirichlet T φ := by
  set L := M + T with hL
  set G : ℕ → ℕ → ℂ := fun m u => shiftedLam n M T m * ex (m * θ) * ex (((m : ℝ) - u) * φ)
    with hG
  have hvan : ∀ u, u < T → ∀ m, m ∉ Ico T L → G m u = 0 := by
    intro u _ m hm
    simp only [hG, shiftedLam]
    rw [if_neg (by rw [mem_Ico] at hm; exact hm)]
    ring
  have hLHS : ∑ s ∈ range L, box n M T θ s * ex (s * φ) = ∑ u ∈ range T, ∑ m ∈ Ico T L, G m u := by
    simp only [box, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun u hu => ?_
    have hu' : u < T := mem_range.mp hu
    have h1 : ∑ s ∈ range L, shiftedLam n M T (s + u) * ex ((s + u : ℕ) * θ) * ex (s * φ)
        = ∑ m ∈ Ico u (u + L), G m u := by
      rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      refine sum_congr rfl fun s _ => ?_
      simp only [hG]
      rw [Nat.add_comm u s]
      congr 2
      push_cast
      ring
    rw [h1]
    refine (sum_subset ?_ fun m hm hm' => hvan u hu' m hm').symm
    intro m hm
    rw [mem_Ico] at hm ⊢
    omega
  have hRHS : ex (T * (θ + φ)) * lamSum n M (θ + φ) * dirichlet T φ
      = ∑ u ∈ range T, ∑ m ∈ Ico T L, G m u := by
    rw [dirichlet, mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [lamSum, mul_sum, sum_mul, sum_Ico_eq_sum_range]
    have hLT : L - T = M := by omega
    rw [hLT]
    refine sum_congr rfl fun m hm => ?_
    have hm' : m < M := mem_range.mp hm
    simp only [hG, shiftedLam]
    rw [if_pos ⟨by omega, by omega⟩, show T + m - T = m by omega]
    have : ex (T * (θ + φ)) * ex (m * (θ + φ)) * ex (-(u * φ))
        = ex ((T + m : ℕ) * θ) * ex ((((T + m : ℕ) : ℝ) - u) * φ) := by
      rw [← ex_add, ← ex_add, ← ex_add]
      congr 1
      push_cast
      ring
    rw [← this]
    ring
  rw [hLHS, hRHS]

/-- The residues `r mod R` with `r/R` within `1/(4T)` of `θ` modulo `1`. -/
def arcSet (R T : ℕ) (θ : ℝ) : Finset ℕ :=
  (range R).filter fun r => ∃ j : ℤ, |(r : ℝ) / R - θ - j| ≤ 1 / (4 * T)

/-- **The arc, pointwise in `n`.** `Σ_{r ∈ arc} |S_n(r/R)|² ≤ (4R/T²) Σ_s |B_s|²`. -/
theorem sum_arc_normSq_le (n M T R : ℕ) (hT : 0 < T) (hR : M + T ≤ R) (θ : ℝ) :
    ∑ r ∈ arcSet R T θ, Complex.normSq (lamSum n M (r / R))
      ≤ 4 * R / (T : ℝ) ^ 2 * ∑ s ∈ range (M + T), Complex.normSq (box n M T θ s) := by
  have hR0 : 0 < R := by omega
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  set c : ℕ → ℂ := fun s => box n M T θ s * ex (-(s * θ)) with hc
  have hpoint : ∀ r ∈ arcSet R T θ, Complex.normSq (lamSum n M (r / R))
      ≤ 4 / (T : ℝ) ^ 2 * Complex.normSq (∑ s ∈ range (M + T), c s * ex (s * r / R)) := by
    intro r hr
    obtain ⟨j, hj⟩ := (mem_filter.mp hr).2
    set φ : ℝ := (r : ℝ) / R - θ - j with hφ
    have hD := half_le_norm_dirichlet hT hj
    have hbox := sum_box_mul_ex n M T θ φ
    have hS : lamSum n M (θ + φ) = lamSum n M (r / R) := by
      have : θ + φ = (r : ℝ) / R + ((-j : ℤ) : ℝ) := by rw [hφ]; push_cast; ring
      rw [this, lamSum_add_int]
    have hsum : ∑ s ∈ range (M + T), box n M T θ s * ex (s * φ)
        = ∑ s ∈ range (M + T), c s * ex (s * r / R) := by
      refine sum_congr rfl fun s _ => ?_
      simp only [hc]
      rw [mul_assoc, ← ex_add]
      have : (s : ℝ) * φ = -(s * θ) + s * r / R + ((-(s * j) : ℤ) : ℝ) := by
        rw [hφ]; push_cast; ring
      rw [this, ex_add_int]
      congr 2
      ring
    rw [hsum, hS] at hbox
    have hnorm : ‖lamSum n M (r / R)‖ * (T / 2) ≤ ‖∑ s ∈ range (M + T), c s * ex (s * r / R)‖ := by
      rw [hbox, norm_mul, norm_mul, norm_ex, one_mul]
      exact mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have h2 : ‖lamSum n M (r / R)‖ ≤ 2 / T * ‖∑ s ∈ range (M + T), c s * ex (s * r / R)‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hTR]
      linarith
    calc ‖lamSum n M (r / R)‖ ^ 2
        ≤ (2 / T * ‖∑ s ∈ range (M + T), c s * ex (s * r / R)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = 4 / (T : ℝ) ^ 2 * ‖∑ s ∈ range (M + T), c s * ex (s * r / R)‖ ^ 2 := by ring
  calc ∑ r ∈ arcSet R T θ, Complex.normSq (lamSum n M (r / R))
      ≤ ∑ r ∈ arcSet R T θ,
          4 / (T : ℝ) ^ 2 * Complex.normSq (∑ s ∈ range (M + T), c s * ex (s * r / R)) :=
        sum_le_sum hpoint
    _ ≤ ∑ r ∈ range R,
          4 / (T : ℝ) ^ 2 * Complex.normSq (∑ s ∈ range (M + T), c s * ex (s * r / R)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
          mul_nonneg (by positivity) (Complex.normSq_nonneg _)
    _ = 4 / (T : ℝ) ^ 2 * (R * ∑ s ∈ range (M + T), Complex.normSq (c s)) := by
        rw [← mul_sum, sum_normSq_eq hR0 hR c]
    _ = 4 * R / (T : ℝ) ^ 2 * ∑ s ∈ range (M + T), Complex.normSq (box n M T θ s) := by
        simp only [hc, Complex.normSq_mul, Complex.normSq_eq_norm_sq (ex _), norm_ex, one_pow,
          mul_one]
        ring

/-- A full box is a shifted window: `|B_s| = |Σ_{u<T} λ(n+(s−T)+u) e(uθ)|` for `T ≤ s ≤ M`. -/
theorem normSq_box_of_full (n M T : ℕ) (θ : ℝ) {s : ℕ} (hs1 : T ≤ s) (hs2 : s ≤ M) :
    Complex.normSq (box n M T θ s)
      = Complex.normSq (∑ u ∈ range T, (lam (n + (s - T) + u) : ℂ) * ex (u * θ)) := by
  have : box n M T θ s = ex (s * θ) * ∑ u ∈ range T, (lam (n + (s - T) + u) : ℂ) * ex (u * θ) := by
    rw [box, mul_sum]
    refine sum_congr rfl fun u hu => ?_
    have hu' := mem_range.mp hu
    rw [shiftedLam, if_pos ⟨by omega, by omega⟩, show n + (s + u - T) = n + (s - T) + u by omega,
      ← mul_assoc, mul_comm (ex _), mul_assoc, ← ex_add]
    congr 2
    push_cast
    ring
  rw [this, Complex.normSq_mul, Complex.normSq_eq_norm_sq (ex _), norm_ex, one_pow, one_mul]

theorem normSq_box_le (n M T : ℕ) (θ : ℝ) (s : ℕ) :
    Complex.normSq (box n M T θ s) ≤ (T : ℝ) ^ 2 := by
  refine normSq_le_sq_of_norm_le ?_
  calc ‖box n M T θ s‖ ≤ ∑ u ∈ range T, ‖shiftedLam n M T (s + u) * ex ((s + u : ℕ) * θ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _u ∈ range T, (1 : ℝ) := by
        refine sum_le_sum fun u _ => ?_
        rw [norm_mul, norm_ex, mul_one, shiftedLam]
        split_ifs
        · rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_lam_le _
        · simp
    _ = T := by simp

/-- **The arc mass.** `R⁻¹ Σ_{r ∈ arc} L(|S_n(r/R)|²)/M ≤ 4V(θ,T)(M+1)/M + 8T/M`. -/
theorem arc_mass_le {U : Ultrafilter ℝ} (hU : (U : Filter ℝ) ≤ atTop) (M T R : ℕ) (hM : 0 < M)
    (hT : 0 < T) (hR : M + T ≤ R) (θ : ℝ) :
    (∑ r ∈ arcSet R T θ, limAvg U (fun n => Complex.normSq (lamSum n M (r / R))) / M) / R
      ≤ 4 * twistVar U θ T * (M + 1) / M + 8 * T / M := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hbox : ∀ s, Bdd fun n => Complex.normSq (box n M T θ s) := fun s =>
    ⟨(T : ℝ) ^ 2, fun n => by
      rw [abs_of_nonneg (Complex.normSq_nonneg _)]
      exact normSq_box_le n M T θ s⟩
  have hwin : Bdd fun n => Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * θ)) :=
    ⟨(T : ℝ) ^ 2, fun n => by
      rw [abs_of_nonneg (Complex.normSq_nonneg _)]
      exact normSq_le_sq_of_norm_le (norm_sum_lam_ex_le n T _ _)⟩
  -- the arc sum under `L`
  have h1 : ∑ r ∈ arcSet R T θ, limAvg U (fun n => Complex.normSq (lamSum n M (r / R)))
      ≤ 4 * R / (T : ℝ) ^ 2 * ∑ s ∈ range (M + T), limAvg U (fun n => Complex.normSq (box n M T θ s)) := by
    rw [← limAvg_sum hU _ fun r _ => bdd_normSq_lamSum M _,
      ← limAvg_sum hU _ fun s _ => hbox s,
      ← limAvg_const_mul hU (bdd_sum _ fun s _ => hbox s)]
    exact limAvg_mono hU (bdd_sum _ fun r _ => bdd_normSq_lamSum M _)
      ((bdd_sum _ fun s _ => hbox s).const_mul _) fun n => sum_arc_normSq_le n M T R hT hR θ
  -- full boxes are windows, partial boxes are at most `T²`
  have hV : twistVar U θ T = ((T : ℝ) ^ 2)⁻¹
      * limAvg U (fun n => Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * θ))) := by
    rw [twistVar, ← limAvg_const_mul hU hwin]
    congr 1
    funext n
    rw [div_eq_inv_mul]
  have hV0 : 0 ≤ twistVar U θ T :=
    limAvg_nonneg hU (hwin.const_mul _ |> fun h => by
      simpa only [div_eq_inv_mul] using h) fun n => div_nonneg (Complex.normSq_nonneg _) (by positivity)
  have hfull : ∀ s ∈ Icc T M,
      limAvg U (fun n => Complex.normSq (box n M T θ s)) = (T : ℝ) ^ 2 * twistVar U θ T := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := mem_Icc.mp hs
    have hcongr : (fun n => Complex.normSq (box n M T θ s))
        = fun n => Complex.normSq (∑ u ∈ range T, (lam (n + (s - T) + u) : ℂ) * ex (u * θ)) := by
      funext n
      exact normSq_box_of_full n M T θ hs1 hs2
    have hshift : limAvg U (fun n => Complex.normSq
          (∑ u ∈ range T, (lam (n + (s - T) + u) : ℂ) * ex (u * θ)))
        = limAvg U (fun n => Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * θ))) :=
      limAvg_shift_add hU hwin (s - T)
    rw [hcongr, hshift, hV]
    field_simp
  have hpart : ∀ s, limAvg U (fun n => Complex.normSq (box n M T θ s)) ≤ (T : ℝ) ^ 2 := by
    intro s
    have := abs_limAvg_le hU (f := fun n => Complex.normSq (box n M T θ s)) fun n => by
      rw [abs_of_nonneg (Complex.normSq_nonneg _)]
      exact normSq_box_le n M T θ s
    exact (le_abs_self _).trans this
  set b : ℕ → ℝ := fun s => limAvg U (fun n => Complex.normSq (box n M T θ s)) with hb
  have hsplit := (sum_filter_add_sum_filter_not (range (M + T)) (fun s => s ∈ Icc T M) b).symm
  have hA : ∑ s ∈ (range (M + T)).filter (fun s => s ∈ Icc T M), b s
      ≤ (M + 1) * ((T : ℝ) ^ 2 * twistVar U θ T) := by
    calc ∑ s ∈ (range (M + T)).filter (fun s => s ∈ Icc T M), b s
        = ∑ _s ∈ (range (M + T)).filter (fun s => s ∈ Icc T M), (T : ℝ) ^ 2 * twistVar U θ T :=
          sum_congr rfl fun s hs => hfull s (mem_filter.mp hs).2
      _ = ((range (M + T)).filter (fun s => s ∈ Icc T M)).card * ((T : ℝ) ^ 2 * twistVar U θ T) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (M + 1) * ((T : ℝ) ^ 2 * twistVar U θ T) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 : ((range (M + T)).filter (fun s => s ∈ Icc T M)).card ≤ (Icc T M).card :=
            card_le_card fun s hs => (mem_filter.mp hs).2
          have h2 : (Icc T M).card ≤ M + 1 := by rw [Nat.card_Icc]; omega
          exact_mod_cast h1.trans h2
  have hB : ∑ s ∈ (range (M + T)).filter (fun s => s ∉ Icc T M), b s ≤ 2 * T * (T : ℝ) ^ 2 := by
    have hsub : (range (M + T)).filter (fun s => s ∉ Icc T M) ⊆ range T ∪ Ico (M + 1) (M + T) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
      rw [mem_range] at hs1
      rw [mem_Icc] at hs2
      rw [mem_union, mem_range, mem_Ico]
      omega
    have hcard : ((range (M + T)).filter (fun s => s ∉ Icc T M)).card ≤ 2 * T := by
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      rw [card_range, Nat.card_Ico]
      omega
    calc ∑ s ∈ (range (M + T)).filter (fun s => s ∉ Icc T M), b s
        ≤ ∑ _s ∈ (range (M + T)).filter (fun s => s ∉ Icc T M), (T : ℝ) ^ 2 :=
          sum_le_sum fun s _ => hpart s
      _ = ((range (M + T)).filter (fun s => s ∉ Icc T M)).card * (T : ℝ) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * T : ℕ) * (T : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 2 * T * (T : ℝ) ^ 2 := by push_cast; ring
  have htot : ∑ s ∈ range (M + T), b s ≤ (M + 1) * ((T : ℝ) ^ 2 * twistVar U θ T)
      + 2 * T * (T : ℝ) ^ 2 := by
    rw [hsplit]
    exact add_le_add hA hB
  rw [← sum_div, div_div, div_le_iff₀ (by positivity)]
  calc ∑ r ∈ arcSet R T θ, limAvg U (fun n => Complex.normSq (lamSum n M (r / R)))
      ≤ 4 * R / (T : ℝ) ^ 2 * ∑ s ∈ range (M + T), b s := h1
    _ ≤ 4 * R / (T : ℝ) ^ 2 * ((M + 1) * ((T : ℝ) ^ 2 * twistVar U θ T)
        + 2 * T * (T : ℝ) ^ 2) := mul_le_mul_of_nonneg_left htot (by positivity)
    _ = (4 * twistVar U θ T * (M + 1) / M + 8 * T / M) * (M * R) := by
        field_simp
        ring

end

end GaloisForLFunctions.LogarithmicChowla
