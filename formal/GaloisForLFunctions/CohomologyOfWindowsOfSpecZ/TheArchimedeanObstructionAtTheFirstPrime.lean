import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.WindowRealizations
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheCanonicalClassOfAWindow

/-!
# The archimedean obstruction at the first prime

The question at the first prime is whether Weil's window form is an identity
`Q = (Lévy jump count) + (a count attached to the fold of T₂) + (squares)`. On a window of length
`log 2 ≤ A < 2 log 2` the ends of every active fold lie in `[−A, −log 2] ∪ [log 2 − A, 0]`; the
**middle** `(−log 2, log 2 − A)`, of length `2 log 2 − A`, is fold-free (`IsFoldFree`). There the
canonical density vanishes (`canonicalDensity_eq_zero_of_middle`) and every fold energy vanishes
(`foldEnergy_eq_zero_of_foldFree`), so

`Q(H) = Ω(0)‖H‖² + J_∞(H) + pole(H)` (`weilQuad_eq_of_foldFree`).

* **The obstruction is infinite-dimensional** (`exists_foldFree_poleFree`): for every finite family of
  linear functionals there is a nonzero fold-free test killed by all of them and by both pole
  pairings; on it `Q − J_∞ = Ω(0)‖H‖² < 0` (`weilQuad_sub_levyJump_lt_zero`).
* **No count identity** (`not_exists_countIdentity`): there is no identity
  `Q = J_∞ + Φ + Σ_{i<k} ℓ_i²` on window tests of such a length with `Φ` any functional of the fold
  data (vanishing on fold-free tests) and finitely many squares of linear functionals.

The exact obstruction at the first prime is therefore archimedean, not arithmetic: the constant
`Ω(0) < 0` on an infinite-dimensional space of fold-free, pole-free tests. The Lévy jump count must
pay it by an inequality (the exit charge of the window, a Poincaré inequality on the middle), never
by an identity with the folds; only after that does the symmetric fold mass of `T₂` enter.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A : ℝ} {H : ℝ → ℝ}

/-- A test is **fold-free** on a window of length `A` when it vanishes off the middle
`(−log 2, log 2 − A)`, where no active fold has an end. -/
def IsFoldFree (A : ℝ) (H : ℝ → ℝ) : Prop :=
  ∀ u, u ∉ Ioo (-Real.log 2) (Real.log 2 - A) → H u = 0

theorem halfChebyshev_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : halfChebyshev x = 0 := by
  have h : ⌊x⌋₊ < 2 := (Nat.floor_lt' (by norm_num)).mpr (by exact_mod_cast hx)
  rw [halfChebyshev, Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- The canonical density vanishes on the middle of a window of length `≥ log 2`. -/
theorem canonicalDensity_eq_zero_of_middle (hA : Real.log 2 ≤ A) {u : ℝ}
    (hu : u ∈ Ioo (-Real.log 2) (Real.log 2 - A)) : canonicalDensity A u = 0 := by
  have hW : u ∈ Icc (-A) 0 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rw [canonicalDensity_eq_halfChebyshev hW,
    halfChebyshev_eq_zero_of_lt_two (x := Real.exp (-u)), halfChebyshev_eq_zero_of_lt_two, add_zero]
  · calc Real.exp (A + u) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by linarith [hu.2])
      _ = 2 := Real.exp_log (by norm_num)
  · calc Real.exp (-u) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by linarith [hu.1])
      _ = 2 := Real.exp_log (by norm_num)

/-- A fold-free test has zero fold energy for every jump of length `≥ log 2`. -/
theorem foldEnergy_eq_zero_of_foldFree (hH : IsFoldFree A H) {ℓ : ℝ} (hℓ : Real.log 2 ≤ ℓ) :
    foldEnergy A ℓ H = 0 := by
  unfold foldEnergy
  have hz : (Icc (-A) (-ℓ)).indicator (fun u => (H u - H (u + ℓ)) ^ 2) = fun _ => 0 := by
    funext u
    by_cases hu : u ∈ Icc (-A) (-ℓ)
    · rw [indicator_of_mem hu, hH u fun hm => by linarith [hm.1, hu.2],
        hH (u + ℓ) fun hm => by linarith [hm.2, hu.1]]
      ring
    · rw [indicator_of_notMem hu]
  rw [hz, integral_zero]

/-- **On fold-free tests Weil's form is archimedean**: `Q = Ω(0)‖H‖² + J_∞ + pole`. -/
theorem weilQuad_eq_of_foldFree (hH : IsWindowTest A H) (hf : IsFoldFree A H)
    (hA : Real.log 2 ≤ A) :
    weilQuad H = EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
      (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) := by
  rw [weilQuad_eq_fold_sub_canonical hH]
  have hF : ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * foldEnergy A (Real.log n) H =
      0 := Finset.sum_eq_zero fun n hn => by
    rw [foldEnergy_eq_zero_of_foldFree hf (Real.log_le_log (by norm_num)
      (by exact_mod_cast (Finset.mem_Icc.mp hn).1)), mul_zero]
  have hk : ∫ u, canonicalDensity A u * H u ^ 2 = 0 := by
    have hz : (fun u => canonicalDensity A u * H u ^ 2) = fun _ => 0 := by
      funext u
      by_cases hu : u ∈ Ioo (-Real.log 2) (Real.log 2 - A)
      · rw [canonicalDensity_eq_zero_of_middle hA hu, zero_mul]
      · rw [hf u hu]; ring
    rw [hz, integral_zero]
  rw [hF, hk]
  ring

/-! ### The pole pairings as linear functionals -/

theorem integrable_mul_continuous (hH : IsWindowTest A H) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable fun u => H u * g u :=
  (hH.continuous.mul hg).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right

/-- The pairing with a continuous weight as a linear functional on window tests. -/
def pairingL (A : ℝ) {g : ℝ → ℝ} (hg : Continuous g) : windowTests A →ₗ[ℝ] ℝ where
  toFun H := ∫ u, (H : ℝ → ℝ) u * g u
  map_add' H G := by
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_mul_continuous H.2 hg) (integrable_mul_continuous G.2 hg)
  map_smul' c H := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _

/-! ### The obstruction -/

/-- **Fold-free, pole-free tests exist in every finite-codimensional subspace**: for
`log 2 ≤ A < 2 log 2` and any `k` linear functionals there is a nonzero fold-free window test killed
by them and by both pole pairings. -/
theorem exists_foldFree_poleFree (hA2 : Real.log 2 ≤ A) (hA4 : A < 2 * Real.log 2) {k : ℕ}
    (ℓ : Fin k → windowTests A →ₗ[ℝ] ℝ) :
    ∃ H : windowTests A, (H : ℝ → ℝ) ≠ 0 ∧ IsFoldFree A H ∧ coshPairing H = 0 ∧
      sinhPairing H = 0 ∧ ∀ i, ℓ i H = 0 := by
  set n := k + 3 with hn_def
  set m := 2 * Real.log 2 - A with hm_def
  have hm : 0 < m := by linarith
  set δ := m / n with hδ_def
  have hn0 : (0 : ℝ) < n := by positivity
  have hδ : 0 < δ := div_pos hm hn0
  have hcell : ∀ i : Fin n, ((i : ℕ) + 1 : ℝ) * δ ≤ m := fun i => by
    have : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    calc (((i : ℕ) : ℝ) + 1) * δ ≤ n * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = m := by rw [hδ_def]; field_simp
  -- the bumps of `n` cells of the middle `(−log 2, log 2 − A)`
  have hmid : ∀ i : Fin n, ∀ y, y ∉ Ioo (-Real.log 2) (Real.log 2 - A) →
      cellBump (Real.log 2) δ hδ i y = 0 := fun i y hy => by
    refine cellBump_eq_zero hδ i fun hm' => hy ⟨?_, ?_⟩
    · have : 0 ≤ ((i : ℕ) : ℝ) * δ := by positivity
      linarith [hm'.1]
    · linarith [hm'.2, hcell i]
  have hbw : ∀ i : Fin n, IsWindowTest A (cellBump (Real.log 2) δ hδ i) := fun i =>
    ⟨(cellBump (Real.log 2) δ hδ i).contDiff, fun y hy => hmid i y fun hm' =>
      hy ⟨by linarith [hm'.1], by linarith [hm'.2]⟩⟩
  let b : Fin n → windowTests A := fun i => ⟨cellBump (Real.log 2) δ hδ i, hbw i⟩
  -- the `k + 2` functionals
  let F : windowTests A →ₗ[ℝ] (Fin k → ℝ) × ℝ × ℝ :=
    (LinearMap.pi ℓ).prod ((pairingL A (g := fun u => 2 * Real.cosh (u / 2)) (by fun_prop)).prod
      (pairingL A (g := fun u => 2 * Real.sinh (u / 2)) (by fun_prop)))
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := F.comp (Fintype.linearCombination ℝ b)) (by
      rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun,
        Module.finrank_self]
      omega))
  rw [LinearMap.mem_ker, LinearMap.comp_apply] at hc
  set Hs : windowTests A := Fintype.linearCombination ℝ b c with hHs
  have hval : ∀ y, (Hs : ℝ → ℝ) y = ∑ i, c i * cellBump (Real.log 2) δ hδ i y := fun y => by
    rw [hHs, Fintype.linearCombination_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hF : ∀ i, ℓ i Hs = 0 := fun i => congrFun (congrArg Prod.fst hc) i
  have hC : coshPairing Hs = 0 := congrArg (fun x => x.2.1) hc
  have hS : sinhPairing Hs = 0 := congrArg (fun x => x.2.2) hc
  refine ⟨Hs, fun h0 => hc0 (eq_zero_of_sum_cellBump (a := Real.log 2) hδ c fun y => ?_),
    fun y hy => ?_, hC, hS, hF⟩
  · rw [← hval, h0]; rfl
  · rw [hval]
    exact Finset.sum_eq_zero fun i _ => by rw [hmid i y hy, mul_zero]

/-- **The archimedean deficit**: on a nonzero fold-free, pole-free test, `Q − J_∞ = Ω(0)‖H‖² < 0`. -/
theorem weilQuad_sub_levyJump_lt_zero (hH : IsWindowTest A H) (hf : IsFoldFree A H)
    (hA : Real.log 2 ≤ A) (hc : coshPairing H = 0) (hs : sinhPairing H = 0) (hne : H ≠ 0) :
    weilQuad H - levyJump H = EF.gammaBracket 0 * (∫ u, H u ^ 2) ∧
      weilQuad H - levyJump H < 0 := by
  have heq : weilQuad H - levyJump H = EF.gammaBracket 0 * (∫ u, H u ^ 2) := by
    rw [weilQuad_eq_of_foldFree hH hf hA, hc, hs]; ring
  refine ⟨heq, ?_⟩
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
    (f := fun u => H u ^ 2) (x := y) (hH.continuous.pow 2)
    (hH.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    (fun u => sq_nonneg (H u)) (pow_ne_zero 2 hy)
  rw [heq]
  exact mul_neg_of_neg_of_pos RHTower.WeilLevyPoleGauss.gammaBracket_zero_lt_zero hpos

/-- **No count identity at the first prime**: for `log 2 ≤ A < 2 log 2` Weil's window form is not
`J_∞ + Φ + Σ_{i<k} ℓ_i²` with `Φ` a functional of the fold data (vanishing on fold-free tests) and
finitely many squares of linear functionals. -/
theorem not_exists_countIdentity (hA2 : Real.log 2 ≤ A) (hA4 : A < 2 * Real.log 2) :
    ¬ ∃ (Φ : (ℝ → ℝ) → ℝ) (k : ℕ) (ℓ : Fin k → windowTests A →ₗ[ℝ] ℝ),
      (∀ H, IsFoldFree A H → Φ H = 0) ∧
        ∀ H : windowTests A, weilQuad H = levyJump H + Φ H + ∑ i, (ℓ i H) ^ 2 := by
  rintro ⟨Φ, k, ℓ, hΦ, hid⟩
  obtain ⟨H, hne, hf, hc, hs, hℓ⟩ := exists_foldFree_poleFree hA2 hA4 ℓ
  have h := hid H
  rw [hΦ _ hf] at h
  simp only [hℓ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    add_zero] at h
  have := (weilQuad_sub_levyJump_lt_zero H.2 hf hA2 hc hs hne).2
  linarith

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
