import GaloisForLFunctions.HTGeometry.MailletLinearGevrey

/-!
# The least Newton bound of a linear operator is rational

The Gevrey order that Maillet's theorem produces is the least `r` for which no coefficient of the
operator present at a shift `μ ≥ 1` has index above `deg Φ_0 + r μ`.  That least `r` is a maximum of
finitely many ratios of integers, hence rational: for each index `j` the condition is hardest at the
*smallest* shift at which `B_j` is present, and there are only finitely many indices.

This is the arithmetic half of the Newton-slope obstruction — an irrational number can never be the
least Newton bound of any operator.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

/-- The Newton condition at level `r`: no coefficient present at a positive shift `μ` has index
above `deg Φ_0 + r μ`. -/
def NewtonBoundedBy {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (r : ℝ) : Prop :=
  ∀ (μ : ℕ) (j : Fin (m + 1)), 1 ≤ μ → PowerSeries.coeff μ (B j) ≠ 0 →
    ((j : ℕ) : ℝ) ≤ (((shiftPolynomial B 0).natDegree : ℕ) : ℝ) + r * μ

/-- The crude bound `m - deg Φ_0` always satisfies the Newton condition. -/
theorem newtonBoundedBy_natSub {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) :
    NewtonBoundedBy B (((m - (shiftPolynomial B 0).natDegree : ℕ) : ℝ)) := by
  intro μ j hμ _
  set d : ℕ := (shiftPolynomial B 0).natDegree with hd
  have hjm : ((j : ℕ) : ℝ) ≤ (m : ℝ) := by
    have : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
    exact_mod_cast this
  have hμ1 : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
  have hstep : (m : ℝ) ≤ (d : ℝ) + ((m - d : ℕ) : ℝ) * μ := by
    have hbase : (m : ℝ) ≤ (d : ℝ) + ((m - d : ℕ) : ℝ) := by
      by_cases h : d ≤ m
      · rw [Nat.cast_sub h]; linarith
      · push Not at h
        have hz : m - d = 0 := by omega
        rw [hz]
        have : (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_of_lt h
        linarith
    have hmul : ((m - d : ℕ) : ℝ) ≤ ((m - d : ℕ) : ℝ) * μ := by
      have hnn : (0 : ℝ) ≤ ((m - d : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hμ1, hnn]
    linarith
  linarith

/-- **The least Newton bound is rational.**  For each index the condition bites at the smallest
shift where that coefficient is present, and there are finitely many indices, so the least admissible
level is a maximum of finitely many ratios of integers. -/
theorem exists_rat_least_newtonBound {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) :
    ∃ q : ℚ, 0 ≤ q ∧ NewtonBoundedBy B (q : ℝ) ∧
      ∀ r : ℝ, 0 ≤ r → NewtonBoundedBy B r → (q : ℝ) ≤ r := by
  classical
  set d : ℕ := (shiftPolynomial B 0).natDegree with hd
  -- the smallest positive shift at which a given coefficient is present
  set P : Fin (m + 1) → Prop := fun j => ∃ μ : ℕ, 1 ≤ μ ∧ PowerSeries.coeff μ (B j) ≠ 0 with hP
  set contribution : Fin (m + 1) → ℚ := fun j =>
    if h : P j then
      max 0 (((j : ℕ) : ℚ) - (d : ℚ)) / ((Nat.find h : ℕ) : ℚ)
    else 0 with hcontrib
  set q : ℚ := max 0 ((Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty contribution)
    with hq
  have hq0 : 0 ≤ q := le_max_left _ _
  have hcontribq : ∀ j, contribution j ≤ q :=
    fun j => le_trans (Finset.le_sup' contribution (Finset.mem_univ j)) (le_max_right _ _)
  refine ⟨q, hq0, ?_, ?_⟩
  · -- the level `q` satisfies the Newton condition
    intro μ j hμ hne
    have hqr : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    have hμ1 : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
    have hμpos : (0 : ℝ) < (μ : ℝ) := by linarith
    by_cases hjd : ((j : ℕ) : ℝ) ≤ (d : ℝ)
    · nlinarith [hqr, hμ1, hjd]
    · push Not at hjd
      have hPj : P j := ⟨μ, hμ, hne⟩
      have hfind : Nat.find hPj ≤ μ := Nat.find_le ⟨hμ, hne⟩
      have hfind1 : 1 ≤ Nat.find hPj := (Nat.find_spec hPj).1
      have hfindpos : (0 : ℝ) < ((Nat.find hPj : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((Nat.find hPj : ℕ) : ℝ) := by exact_mod_cast hfind1
        linarith
      have hcj : contribution j = max 0 (((j : ℕ) : ℚ) - (d : ℚ)) / ((Nat.find hPj : ℕ) : ℚ) := by
        rw [hcontrib]
        simp only [dif_pos hPj]
      have hjq : (((j : ℕ) : ℚ) - (d : ℚ)) / ((Nat.find hPj : ℕ) : ℚ) ≤ q := by
        refine le_trans ?_ (hcontribq j)
        rw [hcj]
        refine div_le_div_of_nonneg_right (le_max_right _ _) ?_
        exact Nat.cast_nonneg _
      have hjq' : (((j : ℕ) : ℝ) - (d : ℝ)) / ((Nat.find hPj : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hjq
      rw [div_le_iff₀ hfindpos] at hjq'
      have hfindr : ((Nat.find hPj : ℕ) : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hfind
      nlinarith [hjq', hfindr, hqr, hjd]
  · -- and it is the least such level
    intro r hr hNewton
    have hqle : ∀ j, (contribution j : ℝ) ≤ r := by
      intro j
      by_cases hPj : P j
      · have hcj : contribution j
            = max 0 (((j : ℕ) : ℚ) - (d : ℚ)) / ((Nat.find hPj : ℕ) : ℚ) := by
          rw [hcontrib]
          simp only [dif_pos hPj]
        obtain ⟨hfind1, hfindne⟩ := Nat.find_spec hPj
        have hfindpos : (0 : ℝ) < ((Nat.find hPj : ℕ) : ℝ) := by
          have : (1 : ℝ) ≤ ((Nat.find hPj : ℕ) : ℝ) := by exact_mod_cast hfind1
          linarith
        have hbound := hNewton (Nat.find hPj) j hfind1 hfindne
        rw [hcj]
        push_cast
        rw [div_le_iff₀ hfindpos]
        by_cases hle : (((j : ℕ) : ℝ) - (d : ℝ)) ≤ 0
        · have hmax : max (0 : ℝ) (((j : ℕ) : ℝ) - (d : ℝ)) = 0 := max_eq_left hle
          rw [hmax]
          nlinarith [hr, hfindpos]
        · push Not at hle
          have hmax : max (0 : ℝ) (((j : ℕ) : ℝ) - (d : ℝ)) = ((j : ℕ) : ℝ) - (d : ℝ) :=
            max_eq_right (le_of_lt hle)
          rw [hmax]
          linarith [hbound]
      · rw [hcontrib]
        simp only [dif_neg hPj]
        exact_mod_cast hr
    have hsup : ((((Finset.univ : Finset (Fin (m + 1))).sup'
        Finset.univ_nonempty contribution : ℚ)) : ℝ) ≤ r := by
      obtain ⟨j, _, hj⟩ :=
        Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (m + 1))) contribution
      rw [hj]
      exact hqle j
    rw [hq]
    push_cast
    exact max_le hr hsup

/-! ### The Gevrey order produced by Maillet is rational -/

/-- **Every formal solution of a linear analytic equation is Gevrey of a rational order.**  Maillet's
theorem at the least Newton bound, which the previous theorem shows is rational. -/
theorem exists_rat_isGevreySeries_of_eulerLinearOp_eq {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) (hΦ : shiftPolynomial B 0 ≠ 0)
    {F G : PowerSeries ℂ} (hG : IsGevreySeries 0 G)
    (hsol : eulerLinearOp B F = G) :
    ∃ q : ℚ, 0 ≤ q ∧ IsGevreySeries ((q : ℚ) : ℝ) F := by
  obtain ⟨q, hq0, hqbound, _⟩ := exists_rat_least_newtonBound B
  have hq0' : (0 : ℝ) ≤ ((q : ℚ) : ℝ) := by exact_mod_cast hq0
  exact ⟨q, hq0, isGevreySeries_of_eulerLinearOp_eq_newton hq0' B hB hΦ hqbound hG hsol⟩

/-- **The exact Gevrey order of a formal solution of a linear analytic equation is at most a
rational number determined by the operator.** -/
theorem exactOrder_le_rat_of_eulerLinearOp_eq {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) (hΦ : shiftPolynomial B 0 ≠ 0)
    {F G : PowerSeries ℂ} (hG : IsGevreySeries 0 G)
    (hsol : eulerLinearOp B F = G) {s : ℝ} (hs : IsExactGevreySeriesOrder F s) :
    ∃ q : ℚ, 0 ≤ q ∧ s ≤ (q : ℝ) := by
  obtain ⟨q, hq0, hgev⟩ := exists_rat_isGevreySeries_of_eulerLinearOp_eq B hB hΦ hG hsol
  refine ⟨q, hq0, ?_⟩
  by_contra hlt
  push Not at hlt
  exact hs.2 ((q : ℚ) : ℝ) hlt hgev

end GaloisForLFunctions.HTGeometry
