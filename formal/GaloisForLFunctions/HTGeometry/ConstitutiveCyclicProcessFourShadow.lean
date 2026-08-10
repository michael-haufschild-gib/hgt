import Mathlib

/-!
# The cyclic unitary process and its four shadows

A finite cyclic unitary process with simple spectrum on the circle and a cyclic unit vector has
moments `mₙ = ∑ⱼ wⱼ λⱼⁿ`.  These moments carry four unlike shadows at once: a rational transfer
function, a positive Gram-rank profile, a recurrent observer orbit, and an open phase lift.  The
first `2r` moments determine the whole process and predict every later response.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset Polynomial

open scoped Matrix

section CyclicProcess

variable {r : ℕ}

/-- The intervention/response moments of the marked cyclic process, equation (2). -/
noncomputable def processMoment (lam : Fin r → ℂ) (w : Fin r → ℝ) (n : ℕ) : ℂ :=
  ∑ j, (w j : ℂ) * (lam j) ^ n

/-- The monic characteristic polynomial of the spectrum, equation (6). -/
noncomputable def spectrumPoly (lam : Fin r → ℂ) : Polynomial ℂ :=
  ∏ j, (Polynomial.X - Polynomial.C (lam j))

theorem spectrumPoly_monic (lam : Fin r → ℂ) : (spectrumPoly lam).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (lam j)

theorem natDegree_spectrumPoly (lam : Fin r → ℂ) : (spectrumPoly lam).natDegree = r := by
  rw [spectrumPoly, natDegree_prod _ _ fun j _ => X_sub_C_ne_zero (lam j)]
  simp

theorem eval_spectrumPoly (lam : Fin r → ℂ) (j : Fin r) : (spectrumPoly lam).eval (lam j) = 0 := by
  rw [spectrumPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

/-- **Equation (7).**  The moments obey the order-`r` recurrence given by the spectrum
polynomial. -/
theorem moment_recurrence (lam : Fin r → ℂ) (w : Fin r → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * processMoment lam w (n + k) = 0 := by
  have hswap : ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * processMoment lam w (n + k)
      = ∑ j, (w j : ℂ) * (lam j) ^ n
        * ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * (lam j) ^ k := by
    have hexp : ∀ k, (spectrumPoly lam).coeff k * processMoment lam w (n + k)
        = ∑ j, (spectrumPoly lam).coeff k * ((w j : ℂ) * (lam j) ^ (n + k)) := by
      intro k
      rw [processMoment, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]
    ring
  rw [hswap]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hev : ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * (lam j) ^ k
      = (spectrumPoly lam).eval (lam j) := by
    rw [eval_eq_sum_range' (n := r + 1) (by rw [natDegree_spectrumPoly]; omega)]
  rw [hev, eval_spectrumPoly, mul_zero]

/-- **Equation (11).**  The withheld response is predicted by the reconstructed recurrence. -/
theorem withheld_prediction (lam : Fin r → ℂ) (w : Fin r → ℝ) :
    processMoment lam w (2 * r)
      = -∑ k ∈ Finset.range r, (spectrumPoly lam).coeff k * processMoment lam w (r + k) := by
  have hlead : (spectrumPoly lam).coeff r = 1 := by
    have hm := (spectrumPoly_monic lam).coeff_natDegree
    rwa [natDegree_spectrumPoly] at hm
  have h := moment_recurrence lam w r
  rw [Finset.sum_range_succ, hlead, one_mul] at h
  have hidx : r + r = 2 * r := by ring
  rw [hidx] at h
  linear_combination h

/-! ### Equation (3) — the rational transfer function -/

/-- **Equation (3).**  The transfer function of the process is rational on the unit disc. -/
theorem tsum_processMoment_mul_pow (lam : Fin r → ℂ) (w : Fin r → ℝ)
    (hlam : ∀ j, ‖lam j‖ = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' n : ℕ, processMoment lam w n * z ^ n = ∑ j, (w j : ℂ) / (1 - lam j * z) := by
  have hnorm : ∀ j, ‖lam j * z‖ < 1 := by
    intro j
    rw [norm_mul, hlam j, one_mul]
    exact hz
  have hfun : ∀ n : ℕ, processMoment lam w n * z ^ n
      = ∑ j, (w j : ℂ) * (lam j * z) ^ n := by
    intro n
    rw [processMoment, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]
    ring
  rw [tsum_congr hfun,
    Summable.tsum_finsetSum fun j _ => (summable_geometric_of_norm_lt_one (hnorm j)).mul_left _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (hnorm j), div_eq_mul_inv]

/-! ### Equation (9) — the Hankel determinant -/

/-- The Hankel matrix of the first `2r − 1` moments. -/
noncomputable def momentHankel (lam : Fin r → ℂ) (w : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => processMoment lam w ((i : ℕ) + (j : ℕ))

theorem momentHankel_eq (lam : Fin r → ℂ) (w : Fin r → ℝ) :
    momentHankel lam w
      = (Matrix.vandermonde lam)ᵀ * Matrix.diagonal (fun j => (w j : ℂ))
        * Matrix.vandermonde lam := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  show processMoment lam w ((i : ℕ) + (j : ℕ)) = _
  rw [processMoment]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_apply, Matrix.vandermonde_apply, Matrix.mul_apply,
    Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq, Matrix.vandermonde_apply, pow_add]
    ring
  · intro l _ hl
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **Equation (9).**  The Hankel determinant factors through the Vandermonde determinant. -/
theorem det_momentHankel (lam : Fin r → ℂ) (w : Fin r → ℝ) :
    (momentHankel lam w).det
      = (Matrix.vandermonde lam).det ^ 2 * ∏ j, (w j : ℂ) := by
  rw [momentHankel_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  ring

/-- **The Hankel matrix is invertible.** -/
theorem det_momentHankel_ne_zero (lam : Fin r → ℂ) (w : Fin r → ℝ)
    (hinj : Function.Injective lam) (hw : ∀ j, 0 < w j) :
    (momentHankel lam w).det ≠ 0 := by
  rw [det_momentHankel]
  refine mul_ne_zero (pow_ne_zero _ ?_) ?_
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  · refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    simpa using ne_of_gt (hw j)

/-! ### Equation (10) and the reconstruction -/

theorem coeff_spectrumPoly_top (lam : Fin r → ℂ) : (spectrumPoly lam).coeff r = 1 := by
  have hm := (spectrumPoly_monic lam).coeff_natDegree
  rwa [natDegree_spectrumPoly] at hm

/-- The recurrence in the form used by the Hankel system. -/
theorem moment_recurrence_fin (lam : Fin r → ℂ) (w : Fin r → ℝ) (n : ℕ) :
    ∑ k : Fin r, (spectrumPoly lam).coeff (k : ℕ) * processMoment lam w (n + (k : ℕ))
      = -processMoment lam w (n + r) := by
  have h := moment_recurrence lam w n
  rw [Finset.sum_range_succ, coeff_spectrumPoly_top, one_mul] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (spectrumPoly lam).coeff k * processMoment lam w (n + k))]
  linear_combination h

/-- **Equation (10).**  The recurrence coefficients solve the Hankel system. -/
theorem hankel_mulVec_coeff (lam : Fin r → ℂ) (w : Fin r → ℝ) (i : Fin r) :
    (momentHankel lam w).mulVec (fun k : Fin r => (spectrumPoly lam).coeff (k : ℕ)) i
      = -processMoment lam w ((i : ℕ) + r) := by
  rw [← moment_recurrence_fin lam w (i : ℕ), Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  show processMoment lam w ((i : ℕ) + (k : ℕ)) * (spectrumPoly lam).coeff (k : ℕ) = _
  ring

/-- **Clause 1 of Theorem 3.1.**  The first `2r` moments determine the recurrence coefficients. -/
theorem coeff_eq_of_moments_eq (lam lam' : Fin r → ℂ) (w w' : Fin r → ℝ)
    (hinj : Function.Injective lam) (hw : ∀ j, 0 < w j)
    (h : ∀ n, n < 2 * r → processMoment lam w n = processMoment lam' w' n) (k : Fin r) :
    (spectrumPoly lam).coeff (k : ℕ) = (spectrumPoly lam').coeff (k : ℕ) := by
  have hH : momentHankel lam w = momentHankel lam' w' := by
    ext i j
    exact h _ (by omega)
  have hsys : (momentHankel lam w).mulVec (fun k : Fin r => (spectrumPoly lam).coeff (k : ℕ))
      = (momentHankel lam w).mulVec (fun k : Fin r => (spectrumPoly lam').coeff (k : ℕ)) := by
    funext i
    rw [hankel_mulVec_coeff, hH, hankel_mulVec_coeff]
    congr 1
    exact h _ (by omega)
  have hdet : (momentHankel lam w).det ≠ 0 := det_momentHankel_ne_zero lam w hinj hw
  have hinjm : Function.Injective (momentHankel lam w).mulVec := by
    intro a b hab
    have hstep : (momentHankel lam w)⁻¹ *ᵥ ((momentHankel lam w) *ᵥ a)
        = (momentHankel lam w)⁻¹ *ᵥ ((momentHankel lam w) *ᵥ b) := by rw [hab]
    simp only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] at hstep
    exact hstep
  exact congrFun (hinjm hsys) k

/-- **Clause 5 of Theorem 3.1.**  The first `2r` moments determine every later moment. -/
theorem processMoment_eq_of_eq_below (lam lam' : Fin r → ℂ) (w w' : Fin r → ℝ)
    (hinj : Function.Injective lam) (hw : ∀ j, 0 < w j)
    (h : ∀ n, n < 2 * r → processMoment lam w n = processMoment lam' w' n) (n : ℕ) :
    processMoment lam w n = processMoment lam' w' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 2 * r
    · exact h n hn
    · have hr : r ≤ n - r := by omega
      have hnr : n - r + r = n := by omega
      have hL := moment_recurrence_fin lam w (n - r)
      have hR := moment_recurrence_fin lam' w' (n - r)
      rw [hnr] at hL hR
      have hterms : ∑ k : Fin r, (spectrumPoly lam).coeff (k : ℕ)
            * processMoment lam w (n - r + (k : ℕ))
          = ∑ k : Fin r, (spectrumPoly lam').coeff (k : ℕ)
            * processMoment lam' w' (n - r + (k : ℕ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coeff_eq_of_moments_eq lam lam' w w' hinj hw h k,
          ih (n - r + (k : ℕ)) (by omega)]
      have : -processMoment lam w n = -processMoment lam' w' n := by
        rw [← hL, ← hR, hterms]
      linear_combination -this

/-- **Clause 2 of Theorem 3.1.**  The spectrum polynomials agree, so the unordered eigenvalue set
is determined. -/
theorem spectrumPoly_eq_of_moments_eq (lam lam' : Fin r → ℂ) (w w' : Fin r → ℝ)
    (hinj : Function.Injective lam) (hw : ∀ j, 0 < w j)
    (h : ∀ n, n < 2 * r → processMoment lam w n = processMoment lam' w' n) :
    spectrumPoly lam = spectrumPoly lam' := by
  refine Polynomial.ext fun k => ?_
  rcases lt_trichotomy k r with hk | hk | hk
  · exact coeff_eq_of_moments_eq lam lam' w w' hinj hw h ⟨k, hk⟩
  · subst hk
    rw [coeff_spectrumPoly_top, coeff_spectrumPoly_top]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_spectrumPoly]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_spectrumPoly]; omega)]

/-- **Clause 3 of Theorem 3.1.**  Given the eigenvalues, the first `r` moments determine the
weights. -/
theorem weights_eq_of_moments_eq (lam : Fin r → ℂ) (w w' : Fin r → ℝ)
    (hinj : Function.Injective lam)
    (h : ∀ n, n < r → processMoment lam w n = processMoment lam w' n) : w = w' := by
  have hV : (Matrix.vandermonde lam)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hd : (Matrix.vandermonde lam)ᵀ *ᵥ (fun j => (w j : ℂ) - (w' j : ℂ))
      = (Matrix.vandermonde lam)ᵀ *ᵥ (fun _ => (0 : ℂ)) := by
    funext i
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    have hzero : ∑ j, (Matrix.vandermonde lam)ᵀ i j * (0 : ℂ) = 0 := by simp
    rw [hzero]
    have hexp : ∑ j, (Matrix.vandermonde lam)ᵀ i j * ((w j : ℂ) - (w' j : ℂ))
        = processMoment lam w (i : ℕ) - processMoment lam w' (i : ℕ) := by
      rw [processMoment, processMoment, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.transpose_apply, Matrix.vandermonde_apply]
      ring
    rw [hexp, h (i : ℕ) i.isLt, sub_self]
  have hinjm : Function.Injective ((Matrix.vandermonde lam)ᵀ).mulVec := by
    intro a b hab
    have hstep : ((Matrix.vandermonde lam)ᵀ)⁻¹ *ᵥ ((Matrix.vandermonde lam)ᵀ *ᵥ a)
        = ((Matrix.vandermonde lam)ᵀ)⁻¹ *ᵥ ((Matrix.vandermonde lam)ᵀ *ᵥ b) := by rw [hab]
    simp only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hV), Matrix.one_mulVec] at hstep
    exact hstep
  have hzero := hinjm hd
  funext j
  have := congrFun hzero j
  have hc : ((w j : ℝ) : ℂ) = ((w' j : ℝ) : ℂ) := by
    have h2 : (w j : ℂ) - (w' j : ℂ) = 0 := this
    linear_combination h2
  exact_mod_cast hc

end CyclicProcess

/-! ## §4 — recurrence of the compact observer and escape of the phase lift -/

section RecurrentObserver

open Filter Topology Pointwise

/-- **Recurrence of a cyclic subgroup of a compact group.**  Powers of any element return to every
neighbourhood of the identity at arbitrarily late times. -/
theorem exists_pow_mem_of_compactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (g : G) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ g ^ n ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ : ∃ W ∈ 𝓝 (1 : G), W * W ⊆ U := by
    obtain ⟨W, hW, hWU⟩ := exists_nhds_one_split hU
    exact ⟨W, hW, by rintro x ⟨a, ha, b, hb, rfl⟩; exact hWU a ha b hb⟩
  set V : Set G := W ∩ (fun x : G => x⁻¹) ⁻¹' W with hV
  have hVnhds : V ∈ 𝓝 (1 : G) := by
    refine Filter.inter_mem hW ?_
    have hc : ContinuousAt (fun x : G => x⁻¹) 1 := (continuous_inv (G := G)).continuousAt
    exact hc.preimage_mem_nhds (by simpa using hW)
  have hVU : ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ U := by
    intro a ha b hb
    exact hWU ⟨a, ha.1, b⁻¹, hb.2, rfl⟩
  set nbhd : G → Set G := fun x => (fun y : G => y * x⁻¹) ⁻¹' V with hnbhd
  have hnbhd_mem : ∀ x : G, nbhd x ∈ 𝓝 x := by
    intro x
    have hc : ContinuousAt (fun y : G => y * x⁻¹) x := (continuous_mul_const x⁻¹).continuousAt
    refine hc.preimage_mem_nhds ?_
    simpa using hVnhds
  obtain ⟨S, -, hS⟩ := isCompact_univ.elim_nhds_subcover nbhd (fun x _ => hnbhd_mem x)
  have hchoose : ∀ k : ℕ, ∃ x ∈ S, g ^ ((k + 1) * (M + 1)) ∈ nbhd x := by
    intro k
    have hmem : g ^ ((k + 1) * (M + 1)) ∈ ⋃ x ∈ S, nbhd x := hS (Set.mem_univ _)
    simpa using hmem
  choose f hfS hfmem using hchoose
  have hcard : S.card < (Finset.range (S.card + 1)).card := by
    rw [Finset.card_range]
    omega
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := f) (fun k _ => hfS k)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(k₂ - k₁) * (M + 1), by nlinarith [Nat.sub_pos_of_lt hlt], ?_⟩
    have hsub : g ^ ((k₂ + 1) * (M + 1)) * (g ^ ((k₁ + 1) * (M + 1)))⁻¹
        = g ^ ((k₂ - k₁) * (M + 1)) := by
      rw [← zpow_natCast g, ← zpow_natCast g, ← zpow_natCast g, ← zpow_neg, ← zpow_add]
      congr 1
      have : k₁ ≤ k₂ := le_of_lt hlt
      push_cast [Nat.cast_sub this]
      ring
    rw [← hsub]
    have e1 : g ^ ((k₂ + 1) * (M + 1)) * (f k₂)⁻¹ ∈ V := hfmem k₂
    have e2 : g ^ ((k₁ + 1) * (M + 1)) * (f k₁)⁻¹ ∈ V := hfmem k₁
    rw [heq] at e2
    have hprod := hVU _ e1 _ e2
    have hrw : (g ^ ((k₂ + 1) * (M + 1)) * (f k₂)⁻¹)
          * (g ^ ((k₁ + 1) * (M + 1)) * (f k₂)⁻¹)⁻¹
        = g ^ ((k₂ + 1) * (M + 1)) * (g ^ ((k₁ + 1) * (M + 1)))⁻¹ := by group
    rwa [hrw] at hprod
  · refine ⟨(k₁ - k₂) * (M + 1), by nlinarith [Nat.sub_pos_of_lt hlt], ?_⟩
    have hsub : g ^ ((k₁ + 1) * (M + 1)) * (g ^ ((k₂ + 1) * (M + 1)))⁻¹
        = g ^ ((k₁ - k₂) * (M + 1)) := by
      rw [← zpow_natCast g, ← zpow_natCast g, ← zpow_natCast g, ← zpow_neg, ← zpow_add]
      congr 1
      have : k₂ ≤ k₁ := le_of_lt hlt
      push_cast [Nat.cast_sub this]
      ring
    rw [← hsub]
    have e1 : g ^ ((k₁ + 1) * (M + 1)) * (f k₁)⁻¹ ∈ V := hfmem k₁
    have e2 : g ^ ((k₂ + 1) * (M + 1)) * (f k₂)⁻¹ ∈ V := hfmem k₂
    rw [← heq] at e2
    have hprod := hVU _ e1 _ e2
    have hrw : (g ^ ((k₁ + 1) * (M + 1)) * (f k₁)⁻¹)
          * (g ^ ((k₂ + 1) * (M + 1)) * (f k₁)⁻¹)⁻¹
        = g ^ ((k₁ + 1) * (M + 1)) * (g ^ ((k₂ + 1) * (M + 1)))⁻¹ := by group
    rwa [hrw] at hprod

/-- **Equation (13).**  The compact observer recurs: at arbitrarily late times every eigenvalue
power is near one, so the response moment returns to its initial value. -/
theorem exists_moment_near_one {r : ℕ} (lam : Fin r → ℂ) (w : Fin r → ℝ)
    (hlam : ∀ j, ‖lam j‖ = 1) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ ‖processMoment lam w n - 1‖ < ε := by
  classical
  set g : Fin r → Circle := fun j => ⟨lam j, by
    show lam j ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    exact hlam j⟩ with hg
  set s : Set Circle := {c : Circle | ‖(c : ℂ) - 1‖ < ε / 2} with hs
  have hsopen : IsOpen s := by
    have hcont : Continuous fun c : Circle => ‖(c : ℂ) - 1‖ := by fun_prop
    exact isOpen_lt hcont continuous_const
  have hsmem : s ∈ 𝓝 (1 : Circle) := by
    refine hsopen.mem_nhds ?_
    show ‖((1 : Circle) : ℂ) - 1‖ < ε / 2
    simp
    linarith
  have hU : Set.pi Set.univ (fun _ : Fin r => s) ∈ 𝓝 (1 : Fin r → Circle) :=
    set_pi_mem_nhds Set.finite_univ fun j _ => hsmem
  obtain ⟨n, hn, hmem⟩ := exists_pow_mem_of_compactSpace g hU M
  refine ⟨n, hn, ?_⟩
  have hcoord : ∀ j, ‖(lam j) ^ n - 1‖ < ε / 2 := by
    intro j
    have hj : (g ^ n) j ∈ s := hmem j (Set.mem_univ j)
    have hval : (((g ^ n) j : Circle) : ℂ) = (lam j) ^ n := by
      show (((g j) ^ n : Circle) : ℂ) = _
      push_cast
      rfl
    rw [hs, Set.mem_setOf_eq, hval] at hj
    exact hj
  have hexp : processMoment lam w n - 1 = ∑ j, (w j : ℂ) * ((lam j) ^ n - 1) := by
    have hone : ∑ j, (w j : ℂ) = 1 := by
      rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one]
    have hsplit : ∑ j, (w j : ℂ) * ((lam j) ^ n - 1)
        = (∑ j, (w j : ℂ) * (lam j) ^ n) - ∑ j, (w j : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit, hone, processMoment]
  rw [hexp]
  have hbound : ‖∑ j, (w j : ℂ) * ((lam j) ^ n - 1)‖ ≤ ∑ j, w j * (ε / 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    exact mul_le_mul_of_nonneg_left (le_of_lt (hcoord j)) (hw j)
  rw [← Finset.sum_mul, hsum, one_mul] at hbound
  linarith

/-- **Equation (14).**  The marked phase lift escapes along any divergent sequence of times. -/
theorem phase_lift_norm (θ : ℝ) (n : ℕ) :
    ‖(n : ℝ) * θ‖ = (n : ℝ) * ‖θ‖ := by
  rw [norm_mul, Real.norm_natCast]

theorem tendsto_phase_lift {θ : ℝ} (hθ : θ ≠ 0) {ns : ℕ → ℕ}
    (hns : Filter.Tendsto ns Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun ℓ => ((ns ℓ : ℝ)) * ‖θ‖) Filter.atTop Filter.atTop := by
  refine Filter.Tendsto.atTop_mul_const (by simpa using hθ) ?_
  exact tendsto_natCast_atTop_atTop.comp hns

end RecurrentObserver

/-! ## §2, equations (4) and (5) — the positive Gram profile -/

section GramRank

open scoped ComplexOrder

variable {r : ℕ}

/-- The weighted coefficient matrix of the orbit `v, Uv, …, U^N v` in the eigenbasis. -/
noncomputable def orbitCoeff (lam : Fin r → ℂ) (w : Fin r → ℝ) (N : ℕ) :
    Matrix (Fin r) (Fin (N + 1)) ℂ :=
  Matrix.of fun k i => ((Real.sqrt (w k) : ℝ) : ℂ) * lam k ^ (i : ℕ)

/-- **Equation (4).**  The Gram matrix of the orbit. -/
noncomputable def momentGram (lam : Fin r → ℂ) (w : Fin r → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (orbitCoeff lam w N)ᴴ * (orbitCoeff lam w N)

/-- **Equation (5), positivity.** -/
theorem momentGram_posSemidef (lam : Fin r → ℂ) (w : Fin r → ℝ) (N : ℕ) :
    (momentGram lam w N).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The Gram entries are the moments of the process. -/
theorem momentGram_apply_of_le (lam : Fin r → ℂ) (w : Fin r → ℝ)
    (hlam : ∀ j, ‖lam j‖ = 1) (hw : ∀ j, 0 ≤ w j) (N : ℕ) {i j : Fin (N + 1)}
    (hij : (i : ℕ) ≤ (j : ℕ)) :
    momentGram lam w N i j = processMoment lam w ((j : ℕ) - (i : ℕ)) := by
  rw [momentGram, Matrix.mul_apply, processMoment]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hconj : (starRingEnd ℂ) (lam k) * lam k = 1 := by
    have h2 : Complex.normSq (lam k) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hlam k]
      norm_num
    rw [mul_comm, Complex.mul_conj, h2]
    norm_num
  have hsq : ((Real.sqrt (w k) : ℝ) : ℂ) * ((Real.sqrt (w k) : ℝ) : ℂ) = ((w k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw k)]
  have hsplit : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by omega
  show (starRingEnd ℂ) (((Real.sqrt (w k) : ℝ) : ℂ) * lam k ^ (i : ℕ))
      * (((Real.sqrt (w k) : ℝ) : ℂ) * lam k ^ (j : ℕ)) = _
  rw [map_mul, Complex.conj_ofReal, map_pow]
  calc ((Real.sqrt (w k) : ℝ) : ℂ) * ((starRingEnd ℂ) (lam k)) ^ (i : ℕ)
        * (((Real.sqrt (w k) : ℝ) : ℂ) * lam k ^ (j : ℕ))
      = (((Real.sqrt (w k) : ℝ) : ℂ) * ((Real.sqrt (w k) : ℝ) : ℂ))
        * (((starRingEnd ℂ) (lam k)) ^ (i : ℕ) * lam k ^ (j : ℕ)) := by ring
    _ = ((w k : ℝ) : ℂ) * (((starRingEnd ℂ) (lam k)) ^ (i : ℕ) * lam k ^ (j : ℕ)) := by rw [hsq]
    _ = ((w k : ℝ) : ℂ) * lam k ^ ((j : ℕ) - (i : ℕ)) := by
        congr 1
        conv_lhs => rw [hsplit, pow_add]
        rw [← mul_assoc, ← mul_pow, hconj, one_pow, one_mul]

/-- The determinant of a weighted Vandermonde matrix. -/
theorem det_weightedVandermonde {n : ℕ} (u v : Fin n → ℂ) :
    (Matrix.of fun k i => u k * v k ^ (i : ℕ) : Matrix (Fin n) (Fin n) ℂ).det
      = (∏ k, u k) * (Matrix.vandermonde v).det := by
  have hfac : (Matrix.of fun k i => u k * v k ^ (i : ℕ) : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal u * Matrix.vandermonde v := by
    ext k i
    rw [Matrix.of_apply, Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, Matrix.vandermonde_apply]
    · intro l _ hl
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal]

/-- **Equation (5), the rank profile.** -/
theorem rank_orbitCoeff (lam : Fin r → ℂ) (w : Fin r → ℝ) (hinj : Function.Injective lam)
    (hw : ∀ j, 0 < w j) (N : ℕ) : (orbitCoeff lam w N).rank = min (N + 1) r := by
  rcases le_total (N + 1) r with hle | hle
  · rw [min_eq_left hle]
    refine le_antisymm (Matrix.rank_le_width _) ?_
    set e : Fin (N + 1) → Fin r := fun i => ⟨(i : ℕ), by omega⟩ with he
    have hdet : ((orbitCoeff lam w N).submatrix e id).det ≠ 0 := by
      have hsub : ((orbitCoeff lam w N).submatrix e id)
          = (Matrix.of fun k i => ((Real.sqrt (w (e k)) : ℝ) : ℂ) * lam (e k) ^ (i : ℕ)
              : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) := rfl
      rw [hsub, det_weightedVandermonde]
      refine mul_ne_zero ?_ ?_
      · refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
        simpa using ne_of_gt (Real.sqrt_pos.mpr (hw (e k)))
      · refine Matrix.det_vandermonde_ne_zero_iff.mpr fun a b hab => ?_
        have h1 := hinj hab
        exact Fin.ext (by simpa [he] using congrArg Fin.val h1)
    have hrk : ((orbitCoeff lam w N).submatrix e id).rank = N + 1 := by
      rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr hdet)), Fintype.card_fin]
    calc N + 1 = ((orbitCoeff lam w N).submatrix e id).rank := hrk.symm
      _ ≤ (orbitCoeff lam w N).rank := Matrix.rank_submatrix_le _ _ _
  · rw [min_eq_right hle]
    refine le_antisymm (Matrix.rank_le_height _) ?_
    set c : Fin r → Fin (N + 1) := fun i => ⟨(i : ℕ), by omega⟩ with hc
    have hdet : ((orbitCoeff lam w N).submatrix id c).det ≠ 0 := by
      have hsub : ((orbitCoeff lam w N).submatrix id c)
          = (Matrix.of fun k i => ((Real.sqrt (w k) : ℝ) : ℂ) * lam k ^ (i : ℕ)
              : Matrix (Fin r) (Fin r) ℂ) := rfl
      rw [hsub, det_weightedVandermonde]
      refine mul_ne_zero ?_ ?_
      · refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
        simpa using ne_of_gt (Real.sqrt_pos.mpr (hw k))
      · exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
    have hrk : ((orbitCoeff lam w N).submatrix id c).rank = r := by
      rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr hdet)), Fintype.card_fin]
    calc r = ((orbitCoeff lam w N).submatrix id c).rank := hrk.symm
      _ ≤ (orbitCoeff lam w N).rank := Matrix.rank_submatrix_le _ _ _

/-- **Equation (5).**  The Gram rank profile of the process. -/
theorem rank_momentGram (lam : Fin r → ℂ) (w : Fin r → ℝ) (hinj : Function.Injective lam)
    (hw : ∀ j, 0 < w j) (N : ℕ) : (momentGram lam w N).rank = min (N + 1) r := by
  rw [momentGram, Matrix.rank_conjTranspose_mul_self, rank_orbitCoeff lam w hinj hw]

/-- **The four shadows of one cyclic process.**  The same moment sequence carries a rational
transfer function, a positive Gram-rank profile, a recurrent observer and an open phase lift, and
its first `2r` moments predict the withheld response. -/
theorem four_shadows {r : ℕ} (lam : Fin r → ℂ) (w : Fin r → ℝ)
    (hlam : ∀ j, ‖lam j‖ = 1) (hinj : Function.Injective lam) (hw : ∀ j, 0 < w j)
    (hsum : ∑ j, w j = 1) (N : ℕ) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    (∀ z : ℂ, ‖z‖ < 1 →
        ∑' n : ℕ, processMoment lam w n * z ^ n = ∑ j, (w j : ℂ) / (1 - lam j * z)) ∧
      (momentGram lam w N).PosSemidef ∧
      (momentGram lam w N).rank = min (N + 1) r ∧
      (∃ n : ℕ, M ≤ n ∧ ‖processMoment lam w n - 1‖ < ε) ∧
      processMoment lam w (2 * r)
        = -∑ k ∈ Finset.range r, (spectrumPoly lam).coeff k * processMoment lam w (r + k) :=
  ⟨fun _ hz => tsum_processMoment_mul_pow lam w hlam hz,
    momentGram_posSemidef lam w N, rank_momentGram lam w hinj hw N,
    exists_moment_near_one lam w hlam (fun j => (hw j).le) hsum hε M,
    withheld_prediction lam w⟩

end GramRank

end GaloisForLFunctions.HTGeometry