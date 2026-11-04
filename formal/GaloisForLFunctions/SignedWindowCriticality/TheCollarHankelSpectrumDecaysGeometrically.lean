import GaloisForLFunctions.SignedWindowCriticality.TheCollarHankelForm
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The spectrum of the collar Hankel form decays geometrically

For collar tests `f` supported in `[p, q]`, `q < m`, `d = m − q`, the collar Hankel form
`𝓗_m(f) = e^m μ_{1/2}(f)² − Σ_k e^{2mσ_k}μ_{σ_k}(f)²` is one pole square against the trivial-zero
squares, and the `k`-th trivial square is at most `‖f‖₁² e^{−(4k+5)d}` (`TheCollarHankelForm`).

* **Finite-codimension bound** (`abs_collarHankel_le_of_moments_zero`,
  `abs_collarHankel_le_sq_of_moments_zero`). On the tests whose pole moment and first `K`
  trivial-zero moments vanish,
  `−(q − p)ε_K‖f‖₂² ≤ 𝓗_m(f) ≤ 0`, `ε_K = e^{−(4K+5)d}/(1 − e^{−4d})`.

* **Infinite negative index** (`exists_collarHankel_negDefinite`). For every `n` there are `n`
  collar tests on whose span `𝓗_m` is negative definite; with at most one positive square
  (`exists_collarHankel_nonpos`) and positivity on nonnegative data beyond the plastic distance
  (`collarHankel_pos_of_nonneg`), the inertia is `(1, ∞)`.

The constraints are `K + 1` continuous linear functionals, so by min–max the collar Hankel form has at
most `K + 1` eigenvalues of modulus above `(q − p)ε_K` on `L²(p, q)`: its spectrum decays at least
geometrically, with ratio `e^{−4d}` per trivial zero, and it is negative semidefinite on the
subspace that annihilates the pole. The ratio is the spacing `2` of the trivial zeros `−2, −4, …`
times twice the distance `d` of the collar to the reflection point.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower

variable {f : ℝ → ℝ} {p q m : ℝ}

/-- **The collar Hankel form on the annihilator of its first `K + 1` moments.** -/
theorem abs_collarHankel_le_of_moments_zero (hf : Continuous f)
    (hsupp : ∀ u, u ∉ Icc p q → f u = 0) (hqm : q < m) (K : ℕ)
    (hpole : leftMoment f (1 / 2) = 0)
    (htriv : ∀ k < K, leftMoment f (trivialExponent k) = 0) :
    collarHankel m f ≤ 0 ∧
      |collarHankel m f| ≤ (∫ u, |f u|) ^ 2 * Real.exp (-(5 * (m - q))) *
        Real.exp (-(4 * (m - q))) ^ K / (1 - Real.exp (-(4 * (m - q)))) := by
  have htr : Real.exp m * leftMoment f (1 / 2) ^ 2 -
      ∑ k ∈ Finset.range K, Real.exp (2 * m * trivialExponent k) *
        leftMoment f (trivialExponent k) ^ 2 = 0 := by
    rw [hpole, Finset.sum_eq_zero fun k hk => by rw [htriv k (Finset.mem_range.mp hk)]; ring]
    ring
  have h := abs_collarHankel_sub_truncation_le (m := m) hf hsupp hqm K
  rw [htr, sub_zero] at h
  refine ⟨?_, h⟩
  unfold collarHankel
  rw [hpole]
  have : 0 ≤ ∑' k : ℕ, Real.exp (2 * m * trivialExponent k) * leftMoment f (trivialExponent k) ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  linarith

/-- Cauchy–Schwarz on a collar: `(∫|f|)² ≤ (q − p)∫f²`. -/
theorem sq_integral_abs_le (hf : Continuous f) (hsupp : ∀ u, u ∉ Icc p q → f u = 0)
    (hpq : p < q) : (∫ u, |f u|) ^ 2 ≤ (q - p) * ∫ u, f u ^ 2 := by
  have e1 : (∫ u, |f u|) = ∫ u in Icc p q, |f u| :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hsupp u hu]).symm
  have e2 : (∫ u, f u ^ 2) = ∫ u in Icc p q, f u ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hsupp u hu]).symm
  rw [e1, e2]
  set I₁ := ∫ u in Icc p q, |f u|
  set I₂ := ∫ u in Icc p q, f u ^ 2
  set L := q - p
  have h1 : IntegrableOn (fun u => |f u|) (Icc p q) := hf.abs.integrableOn_Icc
  have h2 : IntegrableOn (fun u => f u ^ 2) (Icc p q) := (hf.pow 2).integrableOn_Icc
  have hvol : volume.real (Icc p q) = L := by rw [Real.volume_real_Icc_of_le hpq.le]
  -- `0 ≤ ∫(L|f| − I₁)² = L(L I₂ − I₁²)`
  have h0 : 0 ≤ ∫ u in Icc p q, (L * |f u| - I₁) ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hexp : (∫ u in Icc p q, (L * |f u| - I₁) ^ 2) = L * (L * I₂ - I₁ ^ 2) := by
    have e : (fun u => (L * |f u| - I₁) ^ 2) =
        fun u => (L ^ 2 * f u ^ 2 - (2 * L * I₁) * |f u|) + I₁ ^ 2 := by
      funext u; rw [← sq_abs (f u)]; ring
    have hi1 : Integrable (fun u => L ^ 2 * f u ^ 2) (volume.restrict (Icc p q)) :=
      h2.const_mul _
    have hi2 : Integrable (fun u => 2 * L * I₁ * |f u|) (volume.restrict (Icc p q)) :=
      h1.const_mul _
    have hi12 : Integrable (fun u => L ^ 2 * f u ^ 2 - 2 * L * I₁ * |f u|)
        (volume.restrict (Icc p q)) := hi1.sub hi2
    have hi3 : Integrable (fun _ : ℝ => I₁ ^ 2) (volume.restrict (Icc p q)) :=
      integrableOn_const (by simp : volume (Icc p q) ≠ ⊤)
    rw [e, integral_add hi12 hi3, integral_sub hi1 hi2, integral_const_mul, integral_const_mul,
      setIntegral_const, hvol, smul_eq_mul]
    ring
  rw [hexp] at h0
  have hL : 0 < L := by simp only [L]; linarith
  nlinarith

/-- **The collar Hankel form on the annihilator of its first `K + 1` moments, in `L²`.** -/
theorem abs_collarHankel_le_sq_of_moments_zero (hf : Continuous f)
    (hsupp : ∀ u, u ∉ Icc p q → f u = 0) (hpq : p < q) (hqm : q < m) (K : ℕ)
    (hpole : leftMoment f (1 / 2) = 0)
    (htriv : ∀ k < K, leftMoment f (trivialExponent k) = 0) :
    collarHankel m f ≤ 0 ∧
      |collarHankel m f| ≤ (q - p) * (Real.exp (-(5 * (m - q))) *
        Real.exp (-(4 * (m - q))) ^ K / (1 - Real.exp (-(4 * (m - q))))) * ∫ u, f u ^ 2 := by
  obtain ⟨hneg, habs⟩ := abs_collarHankel_le_of_moments_zero hf hsupp hqm K hpole htriv
  refine ⟨hneg, le_trans habs ?_⟩
  have hr : Real.exp (-(4 * (m - q))) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hc : 0 ≤ Real.exp (-(5 * (m - q))) * Real.exp (-(4 * (m - q))) ^ K /
      (1 - Real.exp (-(4 * (m - q)))) :=
    div_nonneg (by positivity) (by linarith)
  have hcs := sq_integral_abs_le hf hsupp hpq
  calc (∫ u, |f u|) ^ 2 * Real.exp (-(5 * (m - q))) * Real.exp (-(4 * (m - q))) ^ K /
        (1 - Real.exp (-(4 * (m - q))))
      = (∫ u, |f u|) ^ 2 * (Real.exp (-(5 * (m - q))) * Real.exp (-(4 * (m - q))) ^ K /
          (1 - Real.exp (-(4 * (m - q))))) := by ring
    _ ≤ ((q - p) * ∫ u, f u ^ 2) * (Real.exp (-(5 * (m - q))) *
          Real.exp (-(4 * (m - q))) ^ K / (1 - Real.exp (-(4 * (m - q))))) :=
        mul_le_mul_of_nonneg_right hcs hc
    _ = _ := by ring

/-! ### Infinite negative index -/

/-- A continuous bump, `1` at `0`, positive exactly on `(−1, 1)`. -/
def unitBump (x : ℝ) : ℝ := Real.smoothTransition (1 - x ^ 2)

theorem continuous_unitBump : Continuous unitBump :=
  Real.smoothTransition.continuous.comp (by fun_prop)

theorem unitBump_nonneg (x : ℝ) : 0 ≤ unitBump x := Real.smoothTransition.nonneg _

theorem unitBump_zero : unitBump 0 = 1 := by simp [unitBump]

theorem unitBump_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : unitBump x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := pow_le_pow_left₀ (by norm_num) hx 2
  rw [sq_abs] at h
  linarith

theorem leftMoment_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℝ) {g : ι → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) (hgc : ∀ i, HasCompactSupport (g i)) (σ : ℝ) :
    leftMoment (fun u => ∑ i ∈ s, c i * g i u) σ = ∑ i ∈ s, c i * leftMoment (g i) σ := by
  unfold leftMoment
  have hi : ∀ i ∈ s, Integrable fun u => c i * (g i u * Real.exp (-(σ * u))) := fun i _ =>
    (((hg i).mul (by fun_prop)).integrable_of_hasCompactSupport (hgc i).mul_right).const_mul _
  beta_reduce
  rw [show (fun u => (∑ i ∈ s, c i * g i u) * Real.exp (-(σ * u))) =
      fun u => ∑ i ∈ s, c i * (g i u * Real.exp (-(σ * u))) from funext fun u => by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring,
    integral_finsetSum s hi]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- **The negative index of the collar Hankel form is infinite.** For every `n` there are `n`
continuous collar tests in `[p, q]` on whose span `𝓗_m` is negative definite: every nonzero
combination has `𝓗_m < 0`. With `exists_collarHankel_nonpos` and `collarHankel_pos_of_nonneg`, the
collar Hankel form has inertia `(1, ∞)` beyond the plastic distance. -/
theorem exists_collarHankel_negDefinite (hpq : p < q) (hqm : q < m) (n : ℕ) :
    ∃ g : Fin n → ℝ → ℝ, (∀ i, Continuous (g i) ∧ ∀ u, u ∉ Icc p q → g i u = 0) ∧
      ∀ c : Fin n → ℝ, c ≠ 0 → collarHankel m (fun u => ∑ i, c i * g i u) < 0 := by
  set δ := (q - p) / ((n : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
  set x : ℕ → ℝ := fun i => p + ((i : ℝ) + 1 / 2) * δ
  set β : ℕ → ℝ → ℝ := fun i u => unitBump ((u - x i) / (δ / 2))
  have hβc : ∀ i, Continuous (β i) := fun i =>
    continuous_unitBump.comp ((continuous_id.sub continuous_const).div_const _)
  -- each bump lives in its own subinterval `[p + iδ, p + (i+1)δ]`
  have hβz : ∀ (i : ℕ) (u : ℝ), (u < p + (i : ℝ) * δ ∨ p + ((i : ℝ) + 1) * δ < u) →
      β i u = 0 := by
    intro i u hu
    apply unitBump_eq_zero
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < δ / 2), le_div_iff₀ (by positivity)]
    rcases hu with hu | hu
    · rw [abs_of_neg (by simp only [x]; nlinarith)]; simp only [x]; nlinarith
    · rw [abs_of_pos (by simp only [x]; nlinarith)]; simp only [x]; nlinarith
  have hβsupp : ∀ i : ℕ, i ≤ n → ∀ u, u ∉ Icc p q → β i u = 0 := by
    intro i hi u hu
    have hq : p + ((i : ℝ) + 1) * δ ≤ q := by
      have : ((i : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hi
      have e : ((n : ℝ) + 1) * δ = q - p := by simp only [δ]; field_simp
      nlinarith
    apply hβz
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · left; nlinarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    · right; linarith
  have hβcs : ∀ i : ℕ, i ≤ n → HasCompactSupport (β i) := fun i hi =>
    HasCompactSupport.intro isCompact_Icc (hβsupp i hi)
  have hβx : ∀ i, β i (x i) = 1 := fun i => by simp [β, unitBump_zero]
  have hβoff : ∀ i j : ℕ, i ≠ j → β i (x j) = 0 := by
    intro i j hij
    apply hβz
    rcases lt_or_gt_of_ne hij with h | h
    · right
      have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      simp only [x]; nlinarith
    · left
      have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      simp only [x]; nlinarith
  -- the pole moment of the reference bump is positive
  have hP0 : 0 < leftMoment (β 0) (1 / 2) := by
    unfold leftMoment
    refine ((hβc 0).mul (by fun_prop)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hβcs 0 (Nat.zero_le n)).mul_right (fun u => mul_nonneg (unitBump_nonneg _)
        (Real.exp_pos _).le) (x := x 0) ?_
    rw [hβx 0, one_mul]; exact (Real.exp_pos _).ne'
  set lam : Fin n → ℝ := fun i => leftMoment (β (i + 1)) (1 / 2) / leftMoment (β 0) (1 / 2)
  set g : Fin n → ℝ → ℝ := fun i u => β (i + 1) u - lam i * β 0 u
  have hgc : ∀ i, Continuous (g i) := fun i => (hβc _).sub (continuous_const.mul (hβc 0))
  have hgs : ∀ i : Fin n, ∀ u, u ∉ Icc p q → g i u = 0 := fun i u hu => by
    simp only [g, hβsupp (i + 1) (by omega) u hu, hβsupp 0 (Nat.zero_le n) u hu, mul_zero, sub_zero]
  have hgcs : ∀ i, HasCompactSupport (g i) := fun i => HasCompactSupport.intro isCompact_Icc (hgs i)
  have hgpole : ∀ i, leftMoment (g i) (1 / 2) = 0 := by
    intro i
    have e : g i = fun u => 1 * β (i + 1) u + (-lam i) * β 0 u := by
      funext u; simp only [g]; ring
    rw [e, leftMoment_add_smul (hβc _) (hβc 0) (hβcs _ (by omega)) (hβcs 0 (Nat.zero_le n))]
    simp only [lam]
    field_simp
    ring
  refine ⟨g, fun i => ⟨hgc i, hgs i⟩, fun c hc => ?_⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  have hF : Continuous fun u => ∑ i, c i * g i u :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hgc i)
  apply collarHankel_neg_of_poleMoment_zero hF
    (fun u hu => Finset.sum_eq_zero fun i _ => by rw [hgs i u hu, mul_zero]) hpq hqm
  · rw [leftMoment_finsetSum _ c hgc hgcs]
    exact Finset.sum_eq_zero fun i _ => by rw [hgpole i, mul_zero]
  · refine ⟨x (j + 1), ?_⟩
    rw [Finset.sum_eq_single j]
    · simp only [g, hβx, hβoff 0 (j + 1) (by omega), mul_zero, sub_zero, mul_one]
      exact hj
    · intro i _ hij
      have hne : (i : ℕ) + 1 ≠ (j : ℕ) + 1 := fun h => hij (Fin.ext (by omega))
      simp only [g, hβoff _ _ hne, hβoff 0 (j + 1) (by omega), mul_zero, sub_zero]
    · intro h; exact absurd (Finset.mem_univ j) h

end GaloisForLFunctions.SignedWindowCriticality

end
