import GaloisForLFunctions.EulerFETransportTheory.MissingResonancesCostLogarithmicDefectEnergy
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakesHavePositiveDensity
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheNormCountOfAnEditIsAConvolution
import GaloisForLFunctions.RHTower.CrystallineProducerRigidity

/-!
# The functional-equation defect of a fake edit

Let `B` be the system of a two-sided edit `e` of the rational primes, with norm multiplicities
`a_n` (`intCoeff`), and suppose `ζ_B` continues to the critical line in the Hamburger strip class
with pole parameter `β` and critical-line FE defect `g` (`HamburgerStripDefect`).

* **Missing multiples** (`intCoeff_editSystem_mul_eq_zero`).  A deleted prime `p` (`e p = -1`)
  divides no norm: `a_{pk} = 0`.  Every fake edit has a least deleted prime
  (`exists_least_deleted_prime`).
* **Abel floor** (`editSystem_eventually_le_mul_abelMass`).  If `e p = -1`, then
  `liminf δ ∫ ‖g‖ e^{-δ|t|} ≥ 1/(3(p + 1))`; so `g` is not Abel-sublinear, does not tend to zero,
  and is not `O((1 + |t|)^{-α})` for any `α > 0`.
* **Logarithmic energy** (`editSystem_fake_defect_energy`).  For a fake edit with count rate
  `β_c < 1`: the density is `A > 0`, the pole parameter is `β = A/2`, and
  `∫ ‖g(t)‖² e^{-|t|/T} dt ≥ A²/(256πp) T log T` for large `T`; hence
  `limsup ‖g(t)‖/√(log|t|) ≥ A/(32√(πp))` and `g` is unbounded.

The count rate gives the density `a_1 + ⋯ + a_n = A n + o(n)` and absolute convergence on
`Re s > 1`; the theorems are the Hamburger-level results of
`UnequalCoefficientsFloorTheAbelMass` and `MissingResonancesCostLogarithmicDefectEnergy`.
-/

open Complex Filter Topology Set
open RHTower RHTower.BeurlingDeletion RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.EulerFETransportTheory
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.FEDefect

open TwoSidedEdits NormCount

/-! ## Norm multiplicities of an integer-norm system -/

/-- The norm multiplicities `a_n` of an integer-norm system, as complex coefficients. -/
def intCoeff (B : BeurlingSystem) (h : HasIntegerNorms B) (n : ℕ) : ℂ := (intCount B h n : ℂ)

/-- `C x^β ≤ η x + C'` on `x ≥ 1` when `β < 1`. -/
theorem exists_mul_rpow_le_mul_add {β : ℝ} (hβ : β < 1) (C : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ, 1 ≤ x → C * x ^ β ≤ η * x + C' := by
  set θ : ℝ := max β 0 with hθ
  have hθ1 : θ < 1 := max_lt hβ one_pos
  have ht : Tendsto (fun x : ℝ => x ^ (-(1 - θ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / (|C| + 1))))
  refine ⟨|C| * max X 1, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : C * x ^ β ≤ |C| * x ^ θ :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _))
        (abs_nonneg C))
  rcases le_or_gt (max X 1) x with hxX | hxX
  · have hpow : x ^ (-(1 - θ)) < η / (|C| + 1) := hX x (le_trans (le_max_left _ _) hxX)
    have e : x ^ θ = x ^ (-(1 - θ)) * x := by
      rw [← Real.rpow_add_one hx0.ne']; congr 1; ring
    have h2 : |C| * x ^ θ ≤ η * x := by
      rw [e]
      have hC1 : |C| * (η / (|C| + 1)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg C]
      calc |C| * (x ^ (-(1 - θ)) * x) = (|C| * x ^ (-(1 - θ))) * x := by ring
        _ ≤ (|C| * (η / (|C| + 1))) * x := by gcongr
        _ ≤ η * x := by gcongr
    linarith [mul_nonneg (abs_nonneg C) (le_trans zero_le_one (le_max_right X 1))]
  · have hxθ : x ^ θ ≤ x := by
      calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ1.le
        _ = x := Real.rpow_one x
    have h2 : |C| * x ^ θ ≤ |C| * max X 1 :=
      mul_le_mul_of_nonneg_left (hxθ.trans hxX.le) (abs_nonneg C)
    nlinarith

/-- A count rate `|N_B(x) - A x| ≤ C x^β`, `β < 1`, gives absolute convergence of
`Σ a_n n^{-s}` on `Re s > 1` and identifies it with `ζ_B`. -/
theorem summable_and_zetaSeriesC_eq_of_count {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) {A C β : ℝ} (hβ : β < 1)
    (hcount : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    (∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖intCoeff B h (n + 1)‖ / ((n : ℝ) + 1) ^ σ) ∧
      ∀ s : ℂ, 1 < s.re → B.zetaSeriesC s = coeffDirichlet (intCoeff B h) s := by
  have hLin := hasLinearCounting_of_count_sub_le hβ.le hcount
  refine ⟨fun σ hσ => ?_, fun s hs => ?_⟩
  · have hL := (zetaSeriesC_eq_LSeries_of_summable h hd (s := (σ : ℂ))
      (by simpa using BeurlingSystem.summable_intNorm_rpow hd hLin hσ)).1
    exact summable_coeff_of_LSeriesSummable hL
  · rw [(zetaSeriesC_eq_LSeries_of_summable h hd
      (BeurlingSystem.summable_intNorm_rpow hd hLin hs)).2, coeffDirichlet_eq_LSeries]
    rfl

/-- A count rate gives the density `a_1 + ⋯ + a_n = A n + o(n)`. -/
theorem density_of_count {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) {A C β : ℝ} (hβ : β < 1)
    (hcount : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    ∀ η : ℝ, 0 < η → ∃ C' : ℝ, ∀ n : ℕ, ‖coeffSum (intCoeff B h) n - A * n‖ ≤ η * n + C' := by
  intro η hη
  obtain ⟨C', hC'0, hC'⟩ := exists_mul_rpow_le_mul_add hβ C hη
  refine ⟨C', fun n => ?_⟩
  have hsum : coeffSum (intCoeff B h) n = ((B.countBall (n : ℝ) : ℝ) : ℂ) := by
    rw [← NormCount.sum_intCount_eq_countBall h hd n, coeffSum, Finset.range_eq_Ico]
    push_cast
    rw [Finset.sum_Ico_add' (fun k => (intCount B h k : ℂ)) 0 n 1]
    rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coeffSum]; exact hC'0
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hsum, show ((B.countBall (n : ℝ) : ℝ) : ℂ) - (A : ℂ) * (n : ℂ) =
      (((B.countBall (n : ℝ) : ℝ) - A * n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact (hcount n hn1).trans (hC' n hn1)

/-- Continuation of `ζ_B` in the Hamburger strip class is continuation of the coefficient series. -/
theorem hamburgerStripDefect_intCoeff {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) {A C β_c : ℝ} (hβ : β_c < 1)
    (hcount : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β_c)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect B.zetaSeriesC β g) :
    HamburgerStripDefect (coeffDirichlet (intCoeff B h)) β g := by
  obtain ⟨E, C₁, hEc, hEd, hdecay, hR, hC, hgm, Cg, N, hgb⟩ := hH
  refine ⟨E, C₁, hEc, hEd, hdecay, fun s hs => ?_, hC, hgm, Cg, N, hgb⟩
  rw [← (summable_and_zetaSeriesC_eq_of_count h hd hβ hcount).2 s (by rw [hs]; norm_num)]
  exact hR s hs

/-! ## The norm multiplicities of an edit -/

theorem intCoeff_editSystem_eq (e : ℕ → ℤ) (n : ℕ) :
    intCoeff (editSystem e) (hasIntegerNorms_editSystem e) n =
      ((freeFn (minusSet e) * freeFn (plusSet e)ᶜ) n : ℂ) := by
  have h := intCount_eq (minusSet e) (plusSet e) n
  unfold intCoeff
  rw [← h]
  rfl

theorem intCoeff_editSystem_one (e : ℕ → ℤ) :
    intCoeff (editSystem e) (hasIntegerNorms_editSystem e) 1 = 1 := by
  rw [intCoeff_editSystem_eq]
  simp [ArithmeticFunction.mul_apply, freeFn_apply, sFreeR_one]

/-- **A deleted prime divides no norm**: `e p = -1` gives `a_{pk} = 0`. -/
theorem intCoeff_editSystem_mul_eq_zero {e : ℕ → ℤ} {p : ℕ} (hp : p.Prime) (hep : e p = -1)
    (k : ℕ) : intCoeff (editSystem e) (hasIntegerNorms_editSystem e) (p * k) = 0 := by
  rw [intCoeff_editSystem_eq, normCount_eq_zero hp (show p ∈ minusSet e from hep)
    (fun h => by have h' : e p = 1 := h; rw [hep] at h'; norm_num at h') (dvd_mul_right p k)]
  simp

/-- **Every fake edit has a least deleted prime.** -/
theorem exists_least_deleted_prime {e : ℕ → ℤ} {β : ℝ} (hβ : β ≤ 1)
    (hf : IsIntegerNormFakeAt (editSystem e) β) :
    ∃ p₀ : ℕ, p₀.Prime ∧ e p₀ = -1 ∧ ∀ q : ℕ, q.Prime → e q = -1 → p₀ ≤ q := by
  classical
  obtain ⟨p, hp, hmiss⟩ := (infinite_missing_primes_of_integerNormFakeAt hβ hf).nonempty
  have hex : ∃ q : ℕ, q.Prime ∧ e q = -1 := by
    refine ⟨p, hp, ?_⟩
    by_contra hne
    have hm : p ∉ minusSet e := hne
    exact hmiss (Sum.inl ⟨p, hp, hm⟩) rfl
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun q hq hqe => Nat.find_min' hex ⟨hq, hqe⟩⟩

/-! ## The defect of an edit with a deleted prime -/

/-- **Abel floor of an edit.**  If `e p = -1` and `ζ_B` continues in the Hamburger strip class,
then `liminf δ ∫ ‖g‖ e^{-δ|t|} ≥ 1/(3(p + 1))`. -/
theorem editSystem_eventually_le_mul_abelMass {e : ℕ → ℤ} {A C β_c : ℝ} (hβc : β_c < 1)
    (hcount : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β_c)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (editSystem e).zetaSeriesC β g)
    {p : ℕ} (hp : p.Prime) (hep : e p = -1) {c : ℝ} (hc : c < 1 / (3 * ((p : ℝ) + 1))) :
    ∀ᶠ δ in 𝓝[>] 0, c ≤ δ * abelMass g δ := by
  have hd := isDiscrete_editSystem e
  have hh := hasIntegerNorms_editSystem e
  have hp0 := intCoeff_editSystem_mul_eq_zero hp hep 1
  rw [mul_one] at hp0
  refine eventually_le_mul_abelMass_of_coeff_ne
    ((summable_and_zetaSeriesC_eq_of_count hh hd hβc hcount).1)
    (hamburgerStripDefect_intCoeff hh hd hβc hcount hH) le_rfl hp.one_lt.le ?_
  rwa [hp0, intCoeff_editSystem_one, zero_sub, norm_neg, norm_one]

/-- **No decaying defect for an edit with a deleted prime.**  The defect is not Abel-sublinear,
does not tend to zero, and is not `O((1 + |t|)^{-α})` for any `α > 0`. -/
theorem editSystem_defect_not_decaying {e : ℕ → ℤ} {A C β_c : ℝ} (hβc : β_c < 1)
    (hcount : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β_c)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (editSystem e).zetaSeriesC β g)
    {p : ℕ} (hp : p.Prime) (hep : e p = -1) :
    ¬ Tendsto (fun δ => δ * abelMass g δ) (𝓝[>] 0) (𝓝 0) ∧
      (¬ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R ≤ |t| → ‖g t‖ ≤ ε) ∧
      ∀ α : ℝ, 0 < α → ∀ C₁ : ℝ, ¬ ∀ t : ℝ, ‖g t‖ ≤ C₁ * (1 + |t|) ^ (-α) := by
  have hd := isDiscrete_editSystem e
  have hh := hasIntegerNorms_editSystem e
  have hsum := (summable_and_zetaSeriesC_eq_of_count hh hd hβc hcount).1
  have hH' := hamburgerStripDefect_intCoeff hh hd hβc hcount hH
  have hp0 := intCoeff_editSystem_mul_eq_zero hp hep 1
  rw [mul_one] at hp0
  have hne : intCoeff (editSystem e) hh 1 ≠ intCoeff (editSystem e) hh p := by
    rw [hp0, intCoeff_editSystem_one]; exact one_ne_zero
  exact ⟨not_tendsto_mul_abelMass_of_coeff_ne hsum hH' le_rfl hp.one_lt.le hne,
    not_tendsto_zero_of_coeff_ne hsum hH' le_rfl hp.one_lt.le hne,
    fun α hα C₁ => not_le_rpow_neg_of_coeff_ne hsum hH' le_rfl hp.one_lt.le hne hα C₁⟩

/-- **The defect energy of a fake edit.**  Let the edit system be an integer-norm fake with count
rate `|N_B(x) - A x| ≤ C x^{β_c}`, `β_c < 1`, continuing in the Hamburger strip class with
parameter `β` and defect `g`, and let `e p = -1`.  Then `A > 0`, `β = A/2`, and for large `T`
`∫ ‖g(t)‖² e^{-|t|/T} dt ≥ A²/(256πp) · T log T`. -/
theorem editSystem_fake_defect_energy {e : ℕ → ℤ} {β_c A C : ℝ} (hβc : β_c < 1)
    (hf : IsIntegerNormFakeAt (editSystem e) β_c)
    (hcount : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β_c)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (editSystem e).zetaSeriesC β g)
    {p : ℕ} (hp : p.Prime) (hep : e p = -1) :
    0 < A ∧ β = A / 2 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      A ^ 2 / (256 * Real.pi * p) * (T * Real.log T) ≤
        ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) := by
  have hd := isDiscrete_editSystem e
  have hh := hasIntegerNorms_editSystem e
  have hsum := (summable_and_zetaSeriesC_eq_of_count hh hd hβc hcount).1
  have hH' := hamburgerStripDefect_intCoeff hh hd hβc hcount hH
  have hN := density_of_count hh hd hβc hcount
  have hA := pos_density_of_integerNormFakeAt_lt_one hf hβc hcount
  exact ⟨hA, pole_eq_half_density hsum hH' hN,
    integral_norm_sq_mul_exp_ge_of_missing_multiples hsum hH' hA hN hp.one_lt.le
      fun k _ => intCoeff_editSystem_mul_eq_zero hp hep k⟩

/-- **A fake edit has an unbounded defect of size at least `√(log|t|)`.**  Under the hypotheses
of `editSystem_fake_defect_energy`, no `c < A/(32√(πp))` has `‖g(t)‖ ≤ c √(log|t|)` for all large
`|t|`, and `g` is unbounded. -/
theorem editSystem_fake_defect_not_le_sqrt_log {e : ℕ → ℤ} {β_c A C : ℝ} (hβc : β_c < 1)
    (hf : IsIntegerNormFakeAt (editSystem e) β_c)
    (hcount : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β_c)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (editSystem e).zetaSeriesC β g)
    {p : ℕ} (hp : p.Prime) (hep : e p = -1) :
    (∀ c : ℝ, c < A / (32 * Real.sqrt (Real.pi * p)) → ∀ t₁ : ℝ,
      ¬ ∀ t : ℝ, t₁ ≤ |t| → ‖g t‖ ≤ c * Real.sqrt (Real.log |t|)) ∧
      ∀ M : ℝ, ¬ ∀ t : ℝ, ‖g t‖ ≤ M := by
  have hd := isDiscrete_editSystem e
  have hh := hasIntegerNorms_editSystem e
  have hsum := (summable_and_zetaSeriesC_eq_of_count hh hd hβc hcount).1
  have hH' := hamburgerStripDefect_intCoeff hh hd hβc hcount hH
  have hN := density_of_count hh hd hβc hcount
  have hA := pos_density_of_integerNormFakeAt_lt_one hf hβc hcount
  have hres : ∀ k : ℕ, 1 ≤ k → intCoeff (editSystem e) hh (p * k) = 0 :=
    fun k _ => intCoeff_editSystem_mul_eq_zero hp hep k
  exact ⟨fun c hc t₁ => not_le_sqrt_log_of_missing_multiples hsum hH' hA hN hp.one_lt.le hres hc t₁,
    fun M => not_bounded_of_missing_multiples hsum hH' hA hN hp.one_lt.le hres M⟩

/-- **The card's form.**  Every fake edit with count rate `β_c < 1` continuing in the Hamburger
strip class has a least deleted prime `p₀`, density `A = 2β > 0`, and
`∫ ‖g‖² e^{-|t|/T} ≥ A²/(256πp₀) T log T` for large `T`. -/
theorem editSystem_fake_least_deleted_prime_energy {e : ℕ → ℤ} {β_c A C : ℝ} (hβc : β_c < 1)
    (hf : IsIntegerNormFakeAt (editSystem e) β_c)
    (hcount : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β_c)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (editSystem e).zetaSeriesC β g) :
    ∃ p₀ : ℕ, p₀.Prime ∧ e p₀ = -1 ∧ (∀ q : ℕ, q.Prime → e q = -1 → p₀ ≤ q) ∧
      (∀ k : ℕ, intCoeff (editSystem e) (hasIntegerNorms_editSystem e) (p₀ * k) = 0) ∧
      0 < A ∧ β = A / 2 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
        A ^ 2 / (256 * Real.pi * p₀) * (T * Real.log T) ≤
          ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) := by
  obtain ⟨p₀, hp₀, hep₀, hmin⟩ := exists_least_deleted_prime hβc.le hf
  exact ⟨p₀, hp₀, hep₀, hmin, intCoeff_editSystem_mul_eq_zero hp₀ hep₀,
    editSystem_fake_defect_energy hβc hf hcount hH hp₀ hep₀⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.FEDefect
