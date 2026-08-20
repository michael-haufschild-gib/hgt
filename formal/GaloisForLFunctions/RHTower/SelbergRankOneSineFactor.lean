/-
# The sine factor of a rank-one gamma presentation

A gamma presentation of rank one -- equivalently, every presentation whose single rate `λ/d` is
`1/2`, which is every degree at most two -- makes the sine factor of the asymmetric functional
equation periodic of period four along the shift lattice.  It cannot vanish at both of the first
two indices, because `sin² + cos² = 1`, so it is frequently bounded below and the card's
"off the exceptional lattice" hypothesis is automatic.

Main results:
* `SelbergGammaData.rank_eq_one_of_halfRate` — a half rate forces rank one.
* `SelbergGammaData.asymmetricS_shift_periodic` — the sine factor has period four in `k`.
* `SelbergGammaData.exists_frequently_le_norm_asymmetricS_shift` —
  **the frequent lower bound, unconditionally**.
* `ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate` —
  **Step 3 with the sine hypothesis discharged**.
-/
import GaloisForLFunctions.RHTower.SelbergShiftRootLaw
import GaloisForLFunctions.HTGeometry.PeriodicFrequentBound

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **A half rate forces rank one.**  The degree is twice the sum of the rates' numerators, so a
presentation all of whose `λ_j` equal `d/2` has exactly one of them. -/
theorem SelbergGammaData.rank_eq_one_of_halfRate (G : SelbergGammaData) (hd : 0 < G.degree)
    (hrate : ∀ j, G.lambda j = G.degree / 2) : G.rank = 1 := by
  have hdeg : G.degree = 2 * ∑ j, G.lambda j := rfl
  have hsum : ∑ j, G.lambda j = (G.rank : ℝ) * (G.degree / 2) := by
    rw [Finset.sum_congr rfl fun j _ => hrate j]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfix : G.degree = (G.rank : ℝ) * G.degree := by
    rw [hsum] at hdeg
    linarith [hdeg]
  have hone : (G.rank : ℝ) = 1 := by
    have : ((G.rank : ℝ) - 1) * G.degree = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hd.ne'
  exact_mod_cast hone

/-- The unique index of a rank-one presentation. -/
def SelbergGammaData.soleIndex (G : SelbergGammaData) (h : G.rank = 1) : Fin G.rank :=
  ⟨0, by omega⟩

theorem SelbergGammaData.eq_soleIndex (G : SelbergGammaData) (h : G.rank = 1)
    (j : Fin G.rank) : j = G.soleIndex h := by
  have hcard : Fintype.card (Fin G.rank) ≤ 1 := by simp [h]
  exact (Fintype.card_le_one_iff.mp hcard) j (G.soleIndex h)

theorem SelbergGammaData.prod_eq_soleIndex (G : SelbergGammaData) (h : G.rank = 1)
    (f : Fin G.rank → ℂ) : ∏ j, f j = f (G.soleIndex h) := by
  refine Finset.prod_eq_single_of_mem (G.soleIndex h) (Finset.mem_univ _) fun b _ hb => ?_
  exact absurd (G.eq_soleIndex h b) hb

/-- **The sine factor has period four along the shift lattice** when the rate is `1/2`. -/
theorem SelbergGammaData.asymmetricS_shift_periodic (G : SelbergGammaData) (hd : 0 < G.degree)
    (hrate : ∀ j, G.lambda j = G.degree / 2) (s₀ : ℂ) (k : ℕ) :
    G.asymmetricS (s₀ - ((k + 4 : ℕ) : ℂ) / (G.degree : ℂ))
      = G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ)) := by
  have hdne : (G.degree : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  unfold SelbergGammaData.asymmetricS
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have hlam : (G.lambda j : ℂ) = (G.degree : ℂ) / 2 := by
    rw [hrate j]
    push_cast
    ring
  have harg : (Real.pi : ℂ)
        * ((G.lambda j : ℂ) * (s₀ - ((k + 4 : ℕ) : ℂ) / (G.degree : ℂ)) + G.mu j)
      = (Real.pi : ℂ) * ((G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) + G.mu j)
        - 2 * (Real.pi : ℂ) := by
    rw [hlam]
    push_cast
    field_simp
    ring
  rw [harg, Complex.sin_sub_two_pi]

/-- **The sine factor cannot vanish at both of the first two indices.** -/
theorem SelbergGammaData.exists_pos_norm_asymmetricS_shift (G : SelbergGammaData)
    (hd : 0 < G.degree) (hrate : ∀ j, G.lambda j = G.degree / 2) (s₀ : ℂ) :
    ∃ k₀ : ℕ, 0 < ‖G.asymmetricS (s₀ - (k₀ : ℂ) / (G.degree : ℂ))‖ := by
  have hrank := G.rank_eq_one_of_halfRate hd hrate
  have hdne : (G.degree : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  set j₀ : Fin G.rank := G.soleIndex hrank with hj₀
  set z : ℂ := (Real.pi : ℂ) * ((G.lambda j₀ : ℂ) * s₀ + G.mu j₀) with hz
  have hlam : (G.lambda j₀ : ℂ) = (G.degree : ℂ) / 2 := by
    rw [hrate j₀]
    push_cast
    ring
  have hzero : G.asymmetricS (s₀ - ((0 : ℕ) : ℂ) / (G.degree : ℂ))
      = (2 : ℂ) ^ G.rank * Complex.sin z := by
    unfold SelbergGammaData.asymmetricS
    rw [G.prod_eq_soleIndex hrank]
    congr 2
    rw [hz]
    push_cast
    ring
  have hone : G.asymmetricS (s₀ - ((1 : ℕ) : ℂ) / (G.degree : ℂ))
      = (2 : ℂ) ^ G.rank * (-Complex.cos z) := by
    unfold SelbergGammaData.asymmetricS
    rw [G.prod_eq_soleIndex hrank]
    congr 1
    have harg : (Real.pi : ℂ)
          * ((G.lambda j₀ : ℂ) * (s₀ - ((1 : ℕ) : ℂ) / (G.degree : ℂ)) + G.mu j₀)
        = z - (Real.pi : ℂ) / 2 := by
      rw [hz, hlam]
      push_cast
      field_simp
      ring
    rw [harg, Complex.sin_sub_pi_div_two]
  by_contra hcon
  have hcon' : ∀ k : ℕ, ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖ ≤ 0 :=
    fun k => not_lt.mp fun h => hcon ⟨k, h⟩
  have h0 : Complex.sin z = 0 := by
    have := hcon' 0
    rw [hzero] at this
    have hnorm : ‖(2 : ℂ) ^ G.rank * Complex.sin z‖ = 0 := le_antisymm this (norm_nonneg _)
    rcases mul_eq_zero.mp (norm_eq_zero.mp hnorm) with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  have h1 : Complex.cos z = 0 := by
    have := hcon' 1
    rw [hone] at this
    have hnorm : ‖(2 : ℂ) ^ G.rank * (-Complex.cos z)‖ = 0 := le_antisymm this (norm_nonneg _)
    rcases mul_eq_zero.mp (norm_eq_zero.mp hnorm) with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · simpa using h
  have := Complex.sin_sq_add_cos_sq z
  rw [h0, h1] at this
  simp at this

/-- **The frequent lower bound on the sine factor, unconditionally**, for a half rate. -/
theorem SelbergGammaData.exists_frequently_le_norm_asymmetricS_shift (G : SelbergGammaData)
    (hd : 0 < G.degree) (hrate : ∀ j, G.lambda j = G.degree / 2) (s₀ : ℂ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ᶠ k : ℕ in atTop,
      c₀ ≤ ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖ := by
  obtain ⟨k₀, hk₀⟩ := G.exists_pos_norm_asymmetricS_shift hd hrate s₀
  refine ⟨‖G.asymmetricS (s₀ - (k₀ : ℂ) / (G.degree : ℂ))‖, hk₀, ?_⟩
  refine frequently_le_of_periodic (f := fun k : ℕ =>
    ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖) (p := 4) (by norm_num) (fun k => ?_) k₀
  show ‖G.asymmetricS (s₀ - ((k + 4 : ℕ) : ℂ) / (G.degree : ℂ))‖
      = ‖G.asymmetricS (s₀ - (k : ℂ) / (G.degree : ℂ))‖
  rw [G.asymmetricS_shift_periodic hd hrate s₀ k]

/-- **Step 3 in every degree, with the sine hypothesis discharged** for a rank-one presentation. -/
theorem ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s₀ : ℂ) (ha1 : (F.coeff 1 : ℂ) ≠ 0)
    (hrate : ∀ j, F.gammaData.lambda j = F.gammaData.degree / 2)
    (hFE : ∀ᶠ k : ℕ in atTop,
      (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)) ∈ F.asymmetricFERegularSet) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) := by
  obtain ⟨c₀, hc₀, hfreq⟩ :=
    F.gammaData.exists_frequently_le_norm_asymmetricS_shift hd hrate s₀
  exact F.limsup_norm_shift_rpow_inv hd s₀ ha1 hFE hc₀ hfreq

end

end RHTower
