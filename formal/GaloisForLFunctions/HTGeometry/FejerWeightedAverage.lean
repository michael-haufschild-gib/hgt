import GaloisForLFunctions.HTGeometry.IndependentTrigProductAverage

/-!
# Fejér-weighted time averages in independent frequencies

For `M` independent frequencies `ω_j`, targets `θ*_j` and `N ≤ M`, the weight
`ψ(t) = ∏_{j<N} F_L(ω_j t - θ*_j)` (Fejér kernels) is real, `0 ≤ ψ ≤ L^N`, and

* `(1/T) ∫₀ᵀ ψ → 1`;
* `(1/T) ∫₀ᵀ ψ(t) e^{±iω_n t} → e^{±iθ*_n} (L-1)/L` for `n < N`;
* `(1/T) ∫₀ᵀ ψ(t) e^{i(ω_m - ω_n)t} → [m = n]` for `N ≤ m, n`.

All three are instances of the product average `prod_trig_time_average` for the shift pattern
`d ∈ {-1,0,1}^M`: `ψ(t) e^{i Σ d_j ω_j t}` is the product of the one-coordinate polynomials
`F_L(x - θ*_j) e^{i d_j x}` (`j < N`) and `e^{i d_j x}` (`j ≥ N`).
-/

open Complex Filter Topology MeasureTheory

namespace RHTower.Weyl

noncomputable section

variable {M : ℕ} (N L : ℕ) (θs : Fin M → ℝ)

/-- Term sets of the shift pattern. -/
def patS (j : Fin M) : Finset (ℕ × ℕ) := if (j : ℕ) < N then fejerSet L else {(0, 0)}

/-- Coefficients of the shift pattern. -/
def patC (j : Fin M) : ℕ × ℕ → ℂ := if (j : ℕ) < N then fejerCoeff L (θs j) else fun _ => 1

/-- Frequencies of the shift pattern `d`. -/
def patK (d : Fin M → ℤ) (j : Fin M) : ℕ × ℕ → ℤ :=
  if (j : ℕ) < N then fejerFreq (d j) else fun _ => d j

/-- The pattern product `ψ(t) e^{i Σ d_j ω_j t}`. -/
def patProd (ω : Fin M → ℝ) (d : Fin M → ℤ) (t : ℝ) : ℂ :=
  ∏ j, trigPoly (patS N L j) (patC N L θs j) (patK N d j) (ω j * t)

/-- The Fejér weight `ψ(t)`. -/
def fejerWeight (ω : Fin M → ℝ) (t : ℝ) : ℂ := patProd N L θs ω 0 t

theorem patProd_eq (ω : Fin M → ℝ) (d : Fin M → ℤ) (t : ℝ) :
    patProd N L θs ω d t =
      fejerWeight N L θs ω t * Complex.exp ((∑ j, ((d j : ℝ) * (ω j * t) : ℝ)) * I) := by
  unfold fejerWeight patProd
  push_cast
  rw [Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold patS patC patK
  split_ifs with hj
  · rw [trigPoly_fejer_shift]; simp
  · rw [trigPoly_mono, trigPoly_mono]; simp

theorem trigConst_pat (hL : 0 < L) (d : Fin M → ℤ) (hd : ∀ j, d j = 0 ∨ d j = 1 ∨ d j = -1)
    (j : Fin M) :
    trigConst (patS N L j) (patC N L θs j) (patK N d j) =
      if (j : ℕ) < N then Complex.exp ((d j : ℝ) * θs j * I) * (((L : ℝ) - |(d j : ℝ)|) / L : ℝ)
      else if d j = 0 then 1 else 0 := by
  unfold patS patC patK
  by_cases hj : (j : ℕ) < N
  · simp only [hj, if_true]; exact trigConst_fejer L hL (θs j) (d j) (hd j)
  · simp only [hj, if_false]; exact trigConst_mono (d j)

/-- **Product average of a shift pattern.** -/
theorem tendsto_patProd (ω : Fin M → ℝ) (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω i = 0 → m = 0)
    (d : Fin M → ℤ) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, patProd N L θs ω d t) atTop
      (𝓝 (∏ j, trigConst (patS N L j) (patC N L θs j) (patK N d j))) :=
  prod_trig_time_average ω hω _ _ _

/-- **The weight has mean one.** -/
theorem tendsto_fejerWeight (hL : 0 < L) (ω : Fin M → ℝ)
    (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω i = 0 → m = 0) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, fejerWeight N L θs ω t) atTop (𝓝 1) := by
  have h := tendsto_patProd N L θs ω hω 0
  have hc : ∏ j, trigConst (patS N L j) (patC N L θs j) (patK N (0 : Fin M → ℤ) j) = 1 := by
    refine Finset.prod_eq_one fun j _ => ?_
    rw [trigConst_pat N L θs hL 0 (fun _ => Or.inl rfl) j]
    have hL0 : L ≠ 0 := hL.ne'
    split_ifs <;> simp_all
  rw [hc] at h
  exact h

/-- **Single shift.** For `n < N` and `s = ±1`, `ψ(t) e^{isω_n t}` averages to `e^{isθ*_n}(L-1)/L`. -/
theorem tendsto_fejerWeight_mul_exp (hL : 0 < L) (ω : Fin M → ℝ)
    (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω i = 0 → m = 0) (n : Fin M) (hn : (n : ℕ) < N)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T,
        fejerWeight N L θs ω t * Complex.exp (((s : ℝ) * (ω n * t) : ℝ) * I)) atTop
      (𝓝 (Complex.exp ((s : ℝ) * θs n * I) * (((L : ℝ) - 1) / L : ℝ))) := by
  classical
  set d : Fin M → ℤ := Pi.single n s with hd
  have hdv : ∀ j, d j = 0 ∨ d j = 1 ∨ d j = -1 := by
    intro j; by_cases hj : j = n
    · subst hj; simp [hd]; tauto
    · simp [hd, hj]
  have h := tendsto_patProd N L θs ω hω d
  have hprod : ∀ t, patProd N L θs ω d t =
      fejerWeight N L θs ω t * Complex.exp (((s : ℝ) * (ω n * t) : ℝ) * I) := by
    intro t
    rw [patProd_eq]
    congr 3
    rw [Finset.sum_eq_single n]
    · simp [hd]
    · intro j _ hjn; simp [hd, hjn]
    · intro h'; exact absurd (Finset.mem_univ n) h'
  simp_rw [hprod] at h
  have hc : ∏ j, trigConst (patS N L j) (patC N L θs j) (patK N d j) =
      Complex.exp ((s : ℝ) * θs n * I) * (((L : ℝ) - 1) / L : ℝ) := by
    rw [Finset.prod_eq_single n]
    · rw [trigConst_pat N L θs hL d hdv n, if_pos hn]
      simp only [hd, Pi.single_eq_same]
      rcases hs with rfl | rfl <;> simp
    · intro j _ hjn
      rw [trigConst_pat N L θs hL d hdv j]
      have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      simp only [hd, Pi.single_eq_of_ne hjn]
      split_ifs <;> simp [hL']
    · intro h'; exact absurd (Finset.mem_univ n) h'
  rw [hc] at h
  exact h

/-- **Pair shift.** For `N ≤ m, n`, `ψ(t) e^{i(ω_m - ω_n)t}` averages to `[m = n]`. -/
theorem tendsto_fejerWeight_mul_pair (hL : 0 < L) (ω : Fin M → ℝ)
    (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω i = 0 → m = 0) (m n : Fin M) (hm : N ≤ (m : ℕ))
    (hn : N ≤ (n : ℕ)) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T,
        fejerWeight N L θs ω t * Complex.exp (((ω m - ω n) * t : ℝ) * I)) atTop
      (𝓝 (if m = n then 1 else 0)) := by
  classical
  by_cases hmn : m = n
  · subst hmn
    simp only [sub_self, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one, if_true]
    exact tendsto_fejerWeight N L θs hL ω hω
  · set d : Fin M → ℤ := Pi.single m 1 - Pi.single n 1 with hd
    have hdm : d m = 1 := by simp [hd, hmn]
    have hdn : d n = -1 := by simp [hd, Ne.symm hmn]
    have hdo : ∀ j, j ≠ m → j ≠ n → d j = 0 := by intro j h1 h2; simp [hd, h1, h2]
    have hdv : ∀ j, d j = 0 ∨ d j = 1 ∨ d j = -1 := by
      intro j
      by_cases h1 : j = m
      · subst h1; right; left; exact hdm
      · by_cases h2 : j = n
        · subst h2; right; right; exact hdn
        · left; exact hdo j h1 h2
    have h := tendsto_patProd N L θs ω hω d
    have hprod : ∀ t, patProd N L θs ω d t =
        fejerWeight N L θs ω t * Complex.exp (((ω m - ω n) * t : ℝ) * I) := by
      intro t
      rw [patProd_eq]
      congr 3
      have hsplit : ∑ j, (d j : ℝ) * (ω j * t) = (d m : ℝ) * (ω m * t) + (d n : ℝ) * (ω n * t) := by
        rw [← Finset.sum_pair (f := fun j => (d j : ℝ) * (ω j * t)) hmn]
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        simp [hdo j hj.1 hj.2]
      rw [hsplit, hdm, hdn]; push_cast; ring
    simp_rw [hprod] at h
    have hc : ∏ j, trigConst (patS N L j) (patC N L θs j) (patK N d j) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
      rw [trigConst_pat N L θs hL d hdv m, if_neg (by omega), if_neg (by rw [hdm]; norm_num)]
    rw [hc] at h
    rw [if_neg hmn]
    exact h

/-- The Fejér weight is real, nonnegative and at most `L^N`. -/
theorem fejerWeight_bounds (hL : 0 < L) (ω : Fin M → ℝ) (t : ℝ) :
    (fejerWeight N L θs ω t).im = 0 ∧ 0 ≤ (fejerWeight N L θs ω t).re ∧
      (fejerWeight N L θs ω t).re ≤ (L : ℝ) ^ N := by
  -- each factor is a nonnegative real at most `L` (Fejér) or equal to `1`
  have hfac : ∀ j : Fin M, ∃ x : ℝ, 0 ≤ x ∧ x ≤ (if (j : ℕ) < N then (L : ℝ) else 1) ∧
      trigPoly (patS N L j) (patC N L θs j) (patK N (0 : Fin M → ℤ) j) (ω j * t) = (x : ℂ) := by
    intro j
    unfold patS patC patK
    split_ifs with hj
    · obtain ⟨him, hre0, hreL⟩ := fejer_zero_re_bounds L hL (θs j) (ω j * t)
      refine ⟨_, hre0, hreL, ?_⟩
      apply Complex.ext <;> simp [him]
    · refine ⟨1, zero_le_one, le_rfl, ?_⟩
      rw [trigPoly_mono]; simp
  choose x hx0 hxb hxe using hfac
  have hprod : fejerWeight N L θs ω t = ((∏ j, x j : ℝ) : ℂ) := by
    unfold fejerWeight patProd; push_cast
    exact Finset.prod_congr rfl fun j _ => hxe j
  rw [hprod]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  refine ⟨Finset.prod_nonneg fun j _ => hx0 j, ?_⟩
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast hL
  calc ∏ j, x j ≤ ∏ j : Fin M, (if (j : ℕ) < N then (L : ℝ) else 1) :=
        Finset.prod_le_prod (fun j _ => hx0 j) (fun j _ => hxb j)
    _ ≤ (L : ℝ) ^ N := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        apply pow_le_pow_right₀ hLpos
        calc (Finset.univ.filter fun j : Fin M => (j : ℕ) < N).card
            ≤ (Finset.range N).card := by
              refine Finset.card_le_card_of_injOn (fun j => (j : ℕ)) (fun j hj => ?_)
                (fun a _ b _ h => Fin.ext h)
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
              simpa using hj
          _ = N := Finset.card_range N

end

end RHTower.Weyl
