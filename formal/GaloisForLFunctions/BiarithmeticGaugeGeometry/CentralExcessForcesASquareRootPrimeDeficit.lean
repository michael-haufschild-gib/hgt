import GaloisForLFunctions.BiarithmeticGaugeGeometry.PositivePrimeMassDeformationsAreRigidOffTheCriticalLine

/-!
# Central Excess Forces a Square-Root Prime Deficit

Let `F` be an **arithmetic member** of `HeightCoupledSystem 2 1 1 γ`: its logarithmic derivative is
a Dirichlet series `−F'/F = Σ b(n) n^{−s}` with nonnegative coefficients (an Euler-product-type
`L`-function with the gamma data of `ζ_γ`). Compare `b` with the coefficients
`b_γ(n) = Λ(n)(2 + 2 cos(γ log n))` of the height-coupled carrier `ζ_γ`: the **surplus**
`s(n) = (b(n) − b_γ(n))⁺` and the **deficit** `d(n) = (b_γ(n) − b(n))⁺` (`n ≥ 2`).

The surplus is a nonnegative measure `Σ s(n) δ_{log n}` on the logarithmic lattice, and the deficit
enters as the holomorphic perturbation `−Σ d(n) n^{−s}`. The perturbed off-line rigidity theorem
therefore gives:

**Square-root deficit law (`centralExcess_forces_squareRoot_deficit`).** If `ξ` has no off-critical
zero at ordinate `γ` and `F` exceeds the central vanishing order of `ζ_γ`, or differs from it at any
zero off the critical line, then the deficit series `Σ d(n) n^{−s}` has abscissa of absolute
convergence at least `1/2`: the prime-power mass that `F` removes from `ζ_γ` is not
`O(x^{1/2 − ε})` for any `ε > 0`. Central vanishing beyond that of `ζ_γ` is paid for by a deficit of
prime mass of at least square-root size, and never by a surplus.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass)

/-! ## §1. Atomic measures on the logarithmic lattice -/

/-- The atomic measure `Σ s(n) δ_{log n}` on the logarithmic lattice. -/
def latticeMeasure (s : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (s n) • Measure.dirac (Real.log n)

/-- Lattice term of the Laplace transform; the atoms `log 0 = log 1 = 0` do not lie in `(0, ∞)`. -/
def latticeLaplaceTerm (s : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then s n * (n : ℝ) ^ (-σ) else 0

theorem laplaceMass_latticeMeasure {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (σ : ℝ) :
    laplaceMass (latticeMeasure s) σ =
      ∑' n : ℕ, ENNReal.ofReal (latticeLaplaceTerm s σ n) := by
  unfold laplaceMass latticeMeasure
  rw [← lintegral_indicator measurableSet_Ioi, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  unfold latticeLaplaceTerm
  by_cases hn : 2 ≤ n
  · have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    have hlog : Real.log n ∈ Ioi (0 : ℝ) := Real.log_pos hn1
    rw [indicator_of_mem hlog, if_pos hn, ← ENNReal.ofReal_mul (hs n),
      Real.rpow_def_of_pos (by linarith), mul_comm (Real.log _) (-σ)]
  · have hlog : Real.log n ∉ Ioi (0 : ℝ) := by
      simp only [mem_Ioi, not_lt]
      interval_cases n <;> simp
    rw [indicator_of_notMem hlog, if_neg hn, mul_zero, ENNReal.ofReal_zero]

theorem latticeLaplaceTerm_nonneg {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (σ : ℝ) (n : ℕ) :
    0 ≤ latticeLaplaceTerm s σ n := by
  unfold latticeLaplaceTerm
  split_ifs
  · exact mul_nonneg (hs n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact le_rfl

/-- For summable lattice terms the Laplace mass is finite and the real transform is the sum. -/
theorem laplace_latticeMeasure {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {σ : ℝ}
    (hsum : Summable (latticeLaplaceTerm s σ)) :
    laplaceMass (latticeMeasure s) σ ≠ ⊤ ∧
      laplaceReal (latticeMeasure s) σ = ∑' n : ℕ, latticeLaplaceTerm s σ n := by
  have hmass : laplaceMass (latticeMeasure s) σ =
      ENNReal.ofReal (∑' n : ℕ, latticeLaplaceTerm s σ n) := by
    rw [laplaceMass_latticeMeasure hs,
      ENNReal.ofReal_tsum_of_nonneg (latticeLaplaceTerm_nonneg hs σ) hsum]
  refine ⟨by rw [hmass]; exact ENNReal.ofReal_ne_top, ?_⟩
  unfold laplaceReal
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun u => (Real.exp_pos _).le)
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-σ * u)).aestronglyMeasurable]
  change (laplaceMass (latticeMeasure s) σ).toReal = _
  rw [hmass, ENNReal.toReal_ofReal (tsum_nonneg (latticeLaplaceTerm_nonneg hs σ))]

/-! ## §2. Surplus and deficit against a comparison lattice -/

/-- Surplus of the coefficients `b` over a comparison sequence `a` (`n ≥ 2`). -/
def relSurplus (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then max (b n - a n) 0 else 0

/-- Deficit of the coefficients `b` below a comparison sequence `a` (`n ≥ 2`). -/
def relDeficit (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then max (a n - b n) 0 else 0

/-- Surplus over the height-coupled lattice `b_γ`. -/
def latticeSurplus (γ : ℝ) (b : ℕ → ℝ) : ℕ → ℝ := relSurplus (heightCoupledVonMangoldt γ) b

/-- Deficit below the height-coupled lattice `b_γ`. -/
def latticeDeficit (γ : ℝ) (b : ℕ → ℝ) : ℕ → ℝ := relDeficit (heightCoupledVonMangoldt γ) b

theorem relSurplus_nonneg (a b : ℕ → ℝ) (n : ℕ) : 0 ≤ relSurplus a b n := by
  unfold relSurplus; split_ifs <;> simp

theorem relDeficit_nonneg (a b : ℕ → ℝ) (n : ℕ) : 0 ≤ relDeficit a b n := by
  unfold relDeficit; split_ifs <;> simp

theorem latticeSurplus_nonneg (γ : ℝ) (b : ℕ → ℝ) (n : ℕ) : 0 ≤ latticeSurplus γ b n :=
  relSurplus_nonneg _ _ n

theorem latticeDeficit_nonneg (γ : ℝ) (b : ℕ → ℝ) (n : ℕ) : 0 ≤ latticeDeficit γ b n :=
  relDeficit_nonneg _ _ n

theorem heightCoupledVonMangoldt_one (γ : ℝ) : heightCoupledVonMangoldt γ 1 = 0 := by
  simp [heightCoupledVonMangoldt]

/-- Termwise splitting `b − a = [n = 1](b(1) − a(1)) + s − d`. -/
theorem sub_eq_relSurplus_sub_relDeficit (a b : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) :
    b n - a n = (if n = 1 then b 1 - a 1 else 0) + relSurplus a b n - relDeficit a b n := by
  unfold relSurplus relDeficit
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    simp
  · rw [if_neg (by omega), if_pos h, if_pos h]
    rcases le_total (b n) (a n) with h' | h'
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

theorem relSurplus_le {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    relSurplus a b n ≤ b n := by
  unfold relSurplus
  split_ifs
  · exact max_le (by linarith [ha n]) (hb n)
  · exact hb n

theorem relDeficit_le {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    relDeficit a b n ≤ a n := by
  unfold relDeficit
  split_ifs
  · exact max_le (by linarith [hb n]) (ha n)
  · exact ha n

theorem summable_norm_term_of_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n)
    {s : ℂ} (hg : LSeriesSummable (fun n => (g n : ℂ)) s) :
    LSeriesSummable (fun n => (f n : ℂ)) s := by
  refine Summable.of_norm_bounded hg.norm fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs
  · exact le_rfl
  · rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hf n), abs_of_nonneg (le_trans (hf n) (hfg n))]
    exact div_le_div_of_nonneg_right (hfg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-! ## §3. The square-root deficit law -/

/-- **Prime-mass split against a comparison lattice.** If `−F'/F = Σ b(n) n^{−s}` and
`−F₀'/F₀ = Σ a(n) n^{−s}` (`a, b ≥ 0`, abscissae `≤ 1`), then on the real ray `σ > 2`,
`−F'/F + F₀'/F₀` is the Laplace transform of the surplus measure `Σ s(n) δ_{log n}` plus
`b(1) − a(1) − Σ d(n) n^{−σ}`, and the surplus measure has finite Laplace mass at `2`. -/
theorem relMember_primeMass_split {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (habsa : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ 1)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1) {F F₀ : ℂ → ℂ}
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hL₀ : ∀ s : ℂ, 1 < s.re → -logDeriv F₀ s = LSeries (fun n => (a n : ℂ)) s) :
    laplaceMass (latticeMeasure (relSurplus a b)) 2 ≠ ⊤ ∧
      ∀ σ : ℝ, 2 < σ →
        -logDeriv F (σ : ℂ) + logDeriv F₀ (σ : ℂ) =
          ((laplaceReal (latticeMeasure (relSurplus a b)) σ : ℝ) : ℂ) +
            ((((b 1 - a 1 : ℝ)) : ℂ) - LSeries (fun n => (relDeficit a b n : ℂ)) σ) := by
  set d : ℕ → ℂ := fun n => (relDeficit a b n : ℂ)
  have hsumm : ∀ σ : ℝ, 1 < σ → Summable (latticeLaplaceTerm (relSurplus a b) σ) := by
    intro σ hσ
    have hbs : LSeriesSummable (fun n => (b n : ℂ)) (σ : ℂ) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt habs (by exact_mod_cast hσ))
    refine Summable.of_nonneg_of_le (latticeLaplaceTerm_nonneg (relSurplus_nonneg a b) σ)
      (fun n => ?_) hbs.norm
    unfold latticeLaplaceTerm
    split_ifs with hn
    · rw [LSeries.norm_term_eq, if_neg (by omega), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hb n), Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (relSurplus_le ha hb n)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · exact norm_nonneg _
  refine ⟨(laplace_latticeMeasure (relSurplus_nonneg a b) (hsumm 2 (by norm_num))).1,
    fun σ hσ => ?_⟩
  have hσ1 : 1 < σ := by linarith
  have hσre : 1 < (σ : ℂ).re := by simpa using hσ1
  rw [hL _ hσre, show logDeriv F₀ (σ : ℂ) = -(-logDeriv F₀ (σ : ℂ)) by ring, hL₀ _ hσre,
    (laplace_latticeMeasure (relSurplus_nonneg a b) (hsumm σ hσ1)).2]
  -- termwise: `b − a = [n = 1](b(1) − a(1)) + s − d`
  have hb' : LSeriesSummable (fun n => (b n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt habs (by exact_mod_cast hσ1))
  have ha' : LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt habsa (by exact_mod_cast hσ1))
  have hd' : LSeriesSummable d (σ : ℂ) :=
    summable_norm_term_of_le (relDeficit_nonneg a b) (relDeficit_le ha hb) ha'
  have hs' : Summable fun n : ℕ => ((latticeLaplaceTerm (relSurplus a b) σ n : ℝ) : ℂ) :=
    Complex.ofRealCLM.summable (hsumm σ hσ1)
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (b n : ℂ)) (σ : ℂ) n -
      LSeries.term (fun n => (a n : ℂ)) (σ : ℂ) n =
      (if n = 1 then (((b 1 - a 1 : ℝ)) : ℂ) else 0) +
        ((latticeLaplaceTerm (relSurplus a b) σ n : ℝ) : ℂ) - LSeries.term d (σ : ℂ) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [latticeLaplaceTerm]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcp : ((n : ℂ)) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hnpos.le]; simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hcp]
    have hsplit := sub_eq_relSurplus_sub_relDeficit a b n hn
    unfold latticeLaplaceTerm
    rcases eq_or_ne n 1 with rfl | hn1
    · have hd1 : d 1 = 0 := by simp [d, relDeficit]
      simp [hd1]
    · rw [if_neg hn1, zero_add] at hsplit ⊢
      have h2 : 2 ≤ n := by omega
      have hsplitC : (b n : ℂ) - (a n : ℂ) =
          (relSurplus a b n : ℂ) - (relDeficit a b n : ℂ) := by exact_mod_cast hsplit
      rw [if_pos h2, Real.rpow_neg hnpos.le, Complex.ofReal_mul, Complex.ofReal_inv,
        ← div_eq_mul_inv, div_sub_div_same, div_sub_div_same, hsplitC]
  have h1 : Summable fun n : ℕ => if n = 1 then (((b 1 - a 1 : ℝ)) : ℂ) else 0 :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      simp only [Finset.mem_singleton] at hn; exact if_neg hn
  have key : LSeries (fun n => (b n : ℂ)) (σ : ℂ) - LSeries (fun n => (a n : ℂ)) (σ : ℂ) =
      ((∑' n : ℕ, latticeLaplaceTerm (relSurplus a b) σ n : ℝ) : ℂ) +
        ((((b 1 - a 1 : ℝ)) : ℂ) - LSeries d σ) := by
    rw [LSeries, LSeries, ← hb'.tsum_sub ha', tsum_congr hterm,
      (h1.add hs').tsum_sub hd', h1.tsum_add hs', tsum_ite_eq, ← Complex.ofReal_tsum, LSeries]
    ring_nf
  linear_combination key

/-- **Prime-mass split of an arithmetic member of the height-coupled class.** If
`−F'/F = Σ b(n) n^{−s}` (`b ≥ 0`, abscissa `≤ 1`), then on the real ray `σ > 2`, `−F'/F + ζ_γ'/ζ_γ`
is the Laplace transform of the surplus measure `Σ s(n) δ_{log n}` plus `b(1) − Σ d(n) n^{−σ}`, and
the surplus measure has finite Laplace mass at `2`. -/
theorem latticeMember_primeMass_split {γ : ℝ} {F : ℂ → ℂ} {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s) :
    laplaceMass (latticeMeasure (latticeSurplus γ b)) 2 ≠ ⊤ ∧
      ∀ σ : ℝ, 2 < σ →
        -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
          ((laplaceReal (latticeMeasure (latticeSurplus γ b)) σ : ℝ) : ℂ) +
            ((b 1 : ℂ) - LSeries (fun n => (latticeDeficit γ b n : ℂ)) σ) := by
  obtain ⟨hmass, hsplit⟩ := relMember_primeMass_split (heightCoupledVonMangoldt_nonneg γ) hb
    (abscissaOfAbsConv_heightCoupledVonMangoldt_le_one γ) habs hL
    (fun s hs => neg_logDeriv_heightCoupledF_eq_LSeries γ hs)
  refine ⟨hmass, fun σ hσ => ?_⟩
  rw [hsplit σ hσ, heightCoupledVonMangoldt_one, sub_zero]
  rfl


/-- **Square-root deficit law.** Let `F ∈ HeightCoupledSystem 2 1 1 γ` with
`−F'/F = Σ b(n) n^{−s}` (`b ≥ 0`, abscissa `≤ 1`). If `ξ` has no off-critical zero at ordinate `γ` and
the deficit series `Σ d(n) n^{−s}` against `ζ_γ` converges absolutely on some half-plane
`Re s > σ_E` with `σ_E < 1/2`, then `Λ` has exactly the zeros of `Λ_γ` off the critical line and
`ord_{1/2} Λ ≤ ord_{1/2} Λ_γ`. -/
theorem latticeMember_offLine_rigid_of_subcritical_deficit {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) < (1 / 2 : ℝ)) :
    (∀ w : ℂ, w.re ≠ 1 / 2 →
        analyticOrderAt Λ w = analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w) ∧
      (analyticOrderAt Λ (1 / 2)).toNat ≤
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat := by
  obtain ⟨σE, hσE1, hσE2⟩ := EReal.exists_between_coe_real hdef
  have hσE : σE < 1 / 2 := by exact_mod_cast hσE2
  have hE : DifferentiableOn ℂ
      (fun s => (b 1 : ℂ) - LSeries (fun n => (latticeDeficit γ b n : ℂ)) s)
      {s : ℂ | σE < s.re} := fun s hs =>
    ((differentiableAt_const _).sub (LSeries_hasDerivAt (lt_trans hσE1
      (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt).differentiableWithinAt
  obtain ⟨hmass, hsplit⟩ := latticeMember_primeMass_split (γ := γ) hb habs hL
  exact perturbedDeformation_offLine_rigid hoff hHC hmass hσE hE hsplit

/-- **Central excess forces a square-root prime deficit.** If `ξ` has no off-critical zero at
ordinate `γ` and an arithmetic member `F` of `HeightCoupledSystem 2 1 1 γ` exceeds the central
vanishing order of `ζ_γ` (or differs from `ζ_γ` at a zero off the critical line), then its deficit
against the height-coupled lattice has abscissa of absolute convergence at least `1/2`. -/
theorem centralExcess_forces_squareRoot_deficit {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hexcess : (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat <
        (analyticOrderAt Λ (1 / 2)).toNat ∨
      ∃ w : ℂ, w.re ≠ 1 / 2 ∧
        analyticOrderAt Λ w ≠ analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w) :
    ((1 / 2 : ℝ) : EReal) ≤ LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hoffline, hcentre⟩ :=
    latticeMember_offLine_rigid_of_subcritical_deficit hoff hHC hb habs hL hlt
  rcases hexcess with h | ⟨w, hw, hne⟩
  · omega
  · exact hne (hoffline w hw)

end GaloisForLFunctions.BiarithmeticGaugeGeometry
