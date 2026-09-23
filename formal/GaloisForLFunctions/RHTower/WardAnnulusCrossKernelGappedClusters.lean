import GaloisForLFunctions.RHTower.WardAnnulusCrossKernelWindowMass

/-!
# Gapped clusters: interpolating between the local survivor and separation

Inside the positivity radius the cross channel costs nothing; beyond it the kernel decays
quadratically, with `|K_A(D)| ≤ M / D ^ 2` for `M = ∑ 2 |c i| (A + b i)`.  A family whose ordinates
are either within the radius of each other or separated by at least `Δ` therefore still has its
quadratic form dominated by the diagonal, up to a loss of order `M / Δ ^ 2` times the squared total
mass.  This covers the gapped-cluster configurations, which no separation hypothesis alone reaches.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Quadratic decay of the cross kernel away from the origin. -/
theorem abs_annulusCrossKernel_le {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A D : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) (hD : D ≠ 0) :
    |annulusCrossKernel S c b A D| ≤ (∑ i ∈ S, 2 * |c i| * (A + b i)) / D ^ (2 : ℕ) := by
  have hD2 : (0 : ℝ) < D ^ (2 : ℕ) := by positivity
  rw [annulusCrossKernel, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hβ := hb i hi
  have hden : (0 : ℝ) < (A + b i) ^ (2 : ℕ) + D ^ (2 : ℕ) := by positivity
  have hnum : |2 * c i * (A + b i)| = 2 * |c i| * (A + b i) := by
    rw [abs_mul, abs_mul, abs_of_pos hβ, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [abs_div, abs_of_pos hden, hnum]
  exact div_le_div_of_nonneg_left (by positivity) hD2 (by nlinarith [sq_nonneg (A + b i)])

/-- **Gapped-cluster domination.**  If every pair of ordinates is either inside the positivity
radius or separated by at least `Δ`, the quadratic form still dominates its diagonal, up to a loss
controlled by the quadratic tail of the kernel. -/
theorem sum_annulusCrossKernel_ge_diagonal_of_gapped {ι J : Type*} (S : Finset ι) (c b : ι → ℝ)
    {A ρ Δ : ℝ} (F : Finset J) (m γ : J → ℝ) (hm : ∀ j ∈ F, 0 ≤ m j)
    (hb : ∀ i ∈ S, 0 < A + b i) (hΔ : 0 < Δ)
    (hnn : ∀ D ∈ Set.Icc (-ρ) ρ, 0 ≤ annulusCrossKernel S c b A D)
    (hdich : ∀ j ∈ F, ∀ k ∈ F, |γ j - γ k| ≤ ρ ∨ Δ ≤ |γ j - γ k|) :
    (∑ j ∈ F, m j ^ (2 : ℕ) * annulusCrossKernel S c b A 0) -
        (∑ i ∈ S, 2 * |c i| * (A + b i)) / Δ ^ (2 : ℕ) * (∑ j ∈ F, m j) ^ (2 : ℕ) ≤
      ∑ j ∈ F, ∑ k ∈ F, m j * m k * annulusCrossKernel S c b A (γ j - γ k) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i ∈ S, 2 * |c i| * (A + b i) := ⟨_, rfl⟩
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact Finset.sum_nonneg fun i hi => by have := hb i hi; positivity
  have hMd : 0 ≤ M / Δ ^ (2 : ℕ) := by positivity
  have hrow : ∀ j ∈ F,
      m j ^ (2 : ℕ) * annulusCrossKernel S c b A 0 - M / Δ ^ (2 : ℕ) * (m j * ∑ k ∈ F, m k) ≤
        ∑ k ∈ F, m j * m k * annulusCrossKernel S c b A (γ j - γ k) := by
    intro j hj
    have hρ0 : (0 : ℝ) ≤ ρ := by
      rcases hdich j hj j hj with h | h
      · simpa using h
      · rw [sub_self, abs_zero] at h; linarith
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun k => |γ j - γ k| ≤ ρ)
      (fun k => m j * m k * annulusCrossKernel S c b A (γ j - γ k))
    have hclose : m j ^ (2 : ℕ) * annulusCrossKernel S c b A 0 ≤
        ∑ k ∈ F.filter (fun k => |γ j - γ k| ≤ ρ),
          m j * m k * annulusCrossKernel S c b A (γ j - γ k) := by
      have hterm : ∀ k ∈ F.filter (fun k => |γ j - γ k| ≤ ρ),
          0 ≤ m j * m k * annulusCrossKernel S c b A (γ j - γ k) := by
        intro k hk
        obtain ⟨hkF, hkP⟩ := Finset.mem_filter.mp hk
        exact mul_nonneg (mul_nonneg (hm j hj) (hm k hkF)) (hnn _ (abs_le.mp hkP))
      have hjmem : j ∈ F.filter (fun k => |γ j - γ k| ≤ ρ) :=
        Finset.mem_filter.mpr ⟨hj, by simpa using hρ0⟩
      have hdiag : m j ^ (2 : ℕ) * annulusCrossKernel S c b A 0 =
          m j * m j * annulusCrossKernel S c b A (γ j - γ j) := by
        rw [sub_self]; ring
      rw [hdiag]
      exact Finset.single_le_sum hterm hjmem
    have hsub : ∑ k ∈ F.filter (fun k => ¬ |γ j - γ k| ≤ ρ), m k ≤ ∑ k ∈ F, m k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k hk _ => hm k hk)
    have hbound : ∀ k ∈ F.filter (fun k => ¬ |γ j - γ k| ≤ ρ),
        -(M / Δ ^ (2 : ℕ)) * (m j * m k) ≤
          m j * m k * annulusCrossKernel S c b A (γ j - γ k) := by
      intro k hk
      obtain ⟨hkF, hkP⟩ := Finset.mem_filter.mp hk
      have hfarD : Δ ≤ |γ j - γ k| := by
        rcases hdich j hj k hkF with h | h
        · exact absurd h hkP
        · exact h
      have hDne : γ j - γ k ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hfarD
        linarith
      have hsq : Δ ^ (2 : ℕ) ≤ (γ j - γ k) ^ (2 : ℕ) := by
        nlinarith [hfarD, hΔ, abs_nonneg (γ j - γ k), sq_abs (γ j - γ k)]
      have habs := abs_annulusCrossKernel_le S c b hb hDne
      rw [← hM] at habs
      have hchain : |annulusCrossKernel S c b A (γ j - γ k)| ≤ M / Δ ^ (2 : ℕ) :=
        habs.trans (div_le_div_of_nonneg_left hMnn (by positivity) hsq)
      have hlow : -(M / Δ ^ (2 : ℕ)) ≤ annulusCrossKernel S c b A (γ j - γ k) := by
        linarith [neg_abs_le (annulusCrossKernel S c b A (γ j - γ k)), hchain]
      have hmm : 0 ≤ m j * m k := mul_nonneg (hm j hj) (hm k hkF)
      nlinarith [hmm, hlow]
    have h1 : ∑ k ∈ F.filter (fun k => ¬ |γ j - γ k| ≤ ρ), -(M / Δ ^ (2 : ℕ)) * (m j * m k) ≤
        ∑ k ∈ F.filter (fun k => ¬ |γ j - γ k| ≤ ρ),
          m j * m k * annulusCrossKernel S c b A (γ j - γ k) :=
      Finset.sum_le_sum hbound
    have h2 : ∑ k ∈ F.filter (fun k => ¬ |γ j - γ k| ≤ ρ), -(M / Δ ^ (2 : ℕ)) * (m j * m k) =
        (-(M / Δ ^ (2 : ℕ)) * m j) * ∑ k ∈ F.filter (fun k => ¬ |γ j - γ k| ≤ ρ), m k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hstep : M / Δ ^ (2 : ℕ) * m j * (∑ k ∈ F.filter (fun k => ¬ |γ j - γ k| ≤ ρ), m k) ≤
        M / Δ ^ (2 : ℕ) * m j * (∑ k ∈ F, m k) :=
      mul_le_mul_of_nonneg_left hsub (mul_nonneg hMd (hm j hj))
    linarith [hsplit, hclose, h1, h2, hstep]
  have hsum := Finset.sum_le_sum hrow
  rw [Finset.sum_sub_distrib] at hsum
  have hfactor : ∑ j ∈ F, M / Δ ^ (2 : ℕ) * (m j * ∑ k ∈ F, m k) =
      M / Δ ^ (2 : ℕ) * (∑ j ∈ F, m j) ^ (2 : ℕ) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hfactor, hM] at hsum
  exact hsum

/-- **Gapped count bound.**  For unit multiplicities the number of ordinates is controlled by the
quadratic form plus the tail loss, with no separation hypothesis inside the positivity radius. -/
theorem card_mul_quantum_le_of_gapped {ι J : Type*} (S : Finset ι) (c b : ι → ℝ)
    {A ρ Δ : ℝ} (F : Finset J) (γ : J → ℝ)
    (hb : ∀ i ∈ S, 0 < A + b i) (hΔ : 0 < Δ)
    (hnn : ∀ D ∈ Set.Icc (-ρ) ρ, 0 ≤ annulusCrossKernel S c b A D)
    (hdich : ∀ j ∈ F, ∀ k ∈ F, |γ j - γ k| ≤ ρ ∨ Δ ≤ |γ j - γ k|) :
    (F.card : ℝ) * annulusCrossKernel S c b A 0 ≤
      (∑ j ∈ F, ∑ k ∈ F, annulusCrossKernel S c b A (γ j - γ k)) +
        (∑ i ∈ S, 2 * |c i| * (A + b i)) / Δ ^ (2 : ℕ) * (F.card : ℝ) ^ (2 : ℕ) := by
  have h := sum_annulusCrossKernel_ge_diagonal_of_gapped S c b F (fun _ => (1 : ℝ)) γ
    (fun _ _ => zero_le_one) hb hΔ hnn hdich
  simp only [one_pow, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  linarith

/-- **Usable gapped count.**  Once the family is small enough for its own gap, namely
`2 M card F ≤ K_A 0 * Δ ^ 2`, the tail loss eats at most half the diagonal and the quadratic form
returns half a quantum per ordinate. -/
theorem half_card_mul_quantum_le_of_gapped {ι J : Type*} (S : Finset ι) (c b : ι → ℝ)
    {A ρ Δ : ℝ} (F : Finset J) (γ : J → ℝ)
    (hb : ∀ i ∈ S, 0 < A + b i) (hΔ : 0 < Δ)
    (hnn : ∀ D ∈ Set.Icc (-ρ) ρ, 0 ≤ annulusCrossKernel S c b A D)
    (hdich : ∀ j ∈ F, ∀ k ∈ F, |γ j - γ k| ≤ ρ ∨ Δ ≤ |γ j - γ k|)
    (hsmall : 2 * (∑ i ∈ S, 2 * |c i| * (A + b i)) * (F.card : ℝ) ≤
      annulusCrossKernel S c b A 0 * Δ ^ (2 : ℕ)) :
    (F.card : ℝ) * annulusCrossKernel S c b A 0 / 2 ≤
      ∑ j ∈ F, ∑ k ∈ F, annulusCrossKernel S c b A (γ j - γ k) := by
  have hbase := card_mul_quantum_le_of_gapped S c b F γ hb hΔ hnn hdich
  have hΔ2 : (0 : ℝ) < Δ ^ (2 : ℕ) := by positivity
  have hcard : (0 : ℝ) ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hloss : (∑ i ∈ S, 2 * |c i| * (A + b i)) / Δ ^ (2 : ℕ) * (F.card : ℝ) ^ (2 : ℕ) ≤
      (F.card : ℝ) * annulusCrossKernel S c b A 0 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hΔ2]
    nlinarith [hsmall, hcard]
  linarith [hbase, hloss]

end

end RHTower
