import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCondensedCentralLimit
import GaloisForLFunctions.HTGeometry.LevyContinuityLimit
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# The Dickman law at the condensation wall

At `σ = 1` put `W_P = (log P)⁻¹ ∑_{p ≤ P} N_p log p`, where the occupation `N_p` of the prime `p`
has
the q-Euler law of the nome `1/p`.  On the atoms of the q-Gamma law, `N_p log p = -(ξ_p - c_p)` with
`c_p = -log(1 - 1/p)`, so `W_P` is the image of the centered socle sum under `y ↦ -y/log P`.

Its characteristic function is `exp ∑_{p ≤ P} ∑_{j,r} p^{-(j+1)(r+1)}(e^{i(r+1)θu_p} - 1)/(r+1)`
with
`u_p = log p/log P`.  The `(1,1)` terms give `∑_{p ≤ P} (e^{iθu_p} - 1)/p`, which converges to
`∫_0^1 (e^{iθu} - 1) du/u` by the Mertens window theorem applied to the continuous quotient
`iθ e^{iθu/2} sinc(θu/2)`; every other term is at most `8|θ| log p/(p² log P)`.  The limit is
continuous at `θ = 0`, so Lévy's continuity theorem produces the Dickman law `D` with
`log E e^{iθD} = ∫_0^1 (e^{iθu} - 1) du/u`, and `W_P ⇒ D`.
-/

open Complex Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The wall statistic -/

/-- The centering `c_p = -log(1 - 1/p)` of the wall coordinates. -/
def wallCentering (p : Nat.Primes) : ℝ := -Real.log (1 - (primeNome one_pos p).val)

/-- On the atoms, `ξ_p - c_p = -N_p log p`. -/
theorem qGammaAtom_sub_wallCentering (p : Nat.Primes) (n : ℕ) :
    qGammaAtom (primeNome one_pos p) n - wallCentering p = -((n : ℝ) * Real.log ((p : ℕ) : ℝ)) := by
  rw [qGammaAtom, wallCentering, log_primeNome]
  ring

/-- The law of `W_P = (log P)⁻¹ ∑_{p ≤ P} N_p log p`. -/
def wallLaw (P : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(soclePrimePartialMeasure one_pos wallCentering P).map (fun y => -y / Real.log P),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

/-- The exponent of the characteristic function of `W_P`. -/
def wallExponent (P : ℕ) (θ : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff P, ∑' jr, (primeNome one_pos p).cumulantTerm (-θ / Real.log P) jr

theorem charFun_wallLaw (P : ℕ) (θ : ℝ) :
    charFun (wallLaw P : Measure ℝ) θ = cexp (wallExponent P θ) := by
  have hmap : charFun (wallLaw P : Measure ℝ) θ
      = charFun (soclePrimePartialMeasure one_pos wallCentering P) (-θ / Real.log P) := by
    rw [charFun_apply_real, charFun_apply_real]
    change ∫ x, cexp ((θ : ℂ) * (x : ℂ) * I) ∂((soclePrimePartialMeasure one_pos wallCentering
      P).map (fun y => -y / Real.log P)) = _
    rw [integral_map (by fun_prop) (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    congr 1
    push_cast
    ring
  rw [hmap, charFun_soclePrimePartialMeasure, wallExponent, Complex.exp_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← qChar_eq_qGammaOn_one_add_I, RealEulerNome.qChar_eq_cexp_cumulant,
    RealEulerNome.cumulant, ← Complex.exp_add, wallCentering]
  congr 1
  push_cast
  ring

/-! ## The leading ladder term and the remainder -/

theorem RealEulerNome.cumulantTerm_zero (q : RealEulerNome) (t : ℝ) :
    q.cumulantTerm t (0, 0) = (q.val : ℂ) * (cexp ((t * Real.log q.val : ℝ) * I) - 1) := by
  rw [RealEulerNome.cumulantTerm]
  push_cast
  ring_nf

theorem RealEulerNome.norm_cumulantTerm_le_mul (q : RealEulerNome) (t : ℝ) (jr : ℕ × ℕ) :
    ‖q.cumulantTerm t jr‖ ≤ |t * Real.log q.val| * q.ladderWeight 0 jr := by
  have hr : (0 : ℝ) < (jr.2 : ℝ) + 1 := by positivity
  have hc : 0 ≤ q.val ^ ((jr.1 + 1) * (jr.2 + 1)) := by have := q.pos; positivity
  rw [RealEulerNome.cumulantTerm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), RealEulerNome.ladderWeight, pow_zero, one_mul]
  have hb : ‖cexp ((((jr.2 : ℝ) + 1) * t * Real.log q.val : ℝ) * I) - 1‖
      ≤ ((jr.2 : ℝ) + 1) * |t * Real.log q.val| := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := ((jr.2 : ℝ) + 1) * t * Real.log q.val)
    rw [mul_comm I] at h
    refine h.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_pos hr]
  calc q.val ^ ((jr.1 + 1) * (jr.2 + 1)) / ((jr.2 : ℝ) + 1)
        * ‖cexp ((((jr.2 : ℝ) + 1) * t * Real.log q.val : ℝ) * I) - 1‖
      ≤ q.val ^ ((jr.1 + 1) * (jr.2 + 1)) / ((jr.2 : ℝ) + 1)
        * (((jr.2 : ℝ) + 1) * |t * Real.log q.val|) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = |t * Real.log q.val| * q.val ^ ((jr.1 + 1) * (jr.2 + 1)) := by field_simp

theorem RealEulerNome.meanSeries_le (q : RealEulerNome) :
    q.meanSeries ≤ q.val / (1 - q.val) ^ 2 := by
  have hq1 : 0 < 1 - q.val := by linarith [q.lt_one]
  have hj : HasSum (fun j : ℕ => q.val ^ (j + 1)) (q.val / (1 - q.val)) := by
    have h := (hasSum_geometric_of_lt_one q.pos.le q.lt_one).mul_left q.val
    rw [← div_eq_mul_inv] at h
    exact h.congr_fun fun j => by ring
  have hr : HasSum (fun r : ℕ => ((r : ℝ) + 1) ^ 0 * q.val ^ r) (1 / (1 - q.val)) := by
    have h := hasSum_geometric_of_lt_one q.pos.le q.lt_one
    rw [← one_div] at h
    exact h.congr_fun fun r => by ring
  have hprod := hj.mul hr (q.summable_ladderMajorant 0)
  have hle : q.meanSeries ≤ q.val / (1 - q.val) * (1 / (1 - q.val)) := by
    rw [RealEulerNome.meanSeries, ← hprod.tsum_eq]
    exact (q.summable_ladderWeight 0).tsum_le_tsum (q.ladderWeight_le_majorant 0)
      (q.summable_ladderMajorant 0)
  calc q.meanSeries ≤ _ := hle
    _ = q.val / (1 - q.val) ^ 2 := by field_simp

/-- The ladder beyond its leading term is at most `|tℓ|(∑ q^{(j+1)(r+1)} - q)`. -/
theorem RealEulerNome.norm_tsum_cumulantTerm_sub_le (q : RealEulerNome) (t : ℝ) :
    ‖(∑' jr, q.cumulantTerm t jr) - q.cumulantTerm t (0, 0)‖
      ≤ |t * Real.log q.val| * (q.meanSeries - q.val) := by
  classical
  have hs := q.summable_cumulantTerm t
  rw [hs.tsum_eq_add_tsum_ite (0, 0), add_sub_cancel_left]
  have hW := q.summable_ladderWeight 0
  have hWsplit := hW.tsum_eq_add_tsum_ite (0, 0)
  have hW0 : q.ladderWeight 0 (0, 0) = q.val := by simp [RealEulerNome.ladderWeight]
  have hbound : ∀ jr : ℕ × ℕ, ‖if jr = (0, 0) then (0 : ℂ) else q.cumulantTerm t jr‖
      ≤ |t * Real.log q.val| * (if jr = (0, 0) then 0 else q.ladderWeight 0 jr) := by
    intro jr
    split_ifs
    · simp
    · exact q.norm_cumulantTerm_le_mul t jr
  have hWite : Summable fun jr : ℕ × ℕ => if jr = (0, 0) then (0 : ℝ) else q.ladderWeight 0 jr :=
    Summable.of_nonneg_of_le (fun jr => by split_ifs; exacts [le_rfl, q.ladderWeight_nonneg 0 jr])
      (fun jr => by split_ifs; exacts [q.ladderWeight_nonneg 0 jr, le_rfl]) hW
  have hmaj := hWite.mul_left |t * Real.log q.val|
  have hnorm : Summable fun jr : ℕ × ℕ =>
      ‖if jr = (0, 0) then (0 : ℂ) else q.cumulantTerm t jr‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmaj
  calc ‖∑' jr, if jr = (0, 0) then (0 : ℂ) else q.cumulantTerm t jr‖
      ≤ ∑' jr, ‖if jr = (0, 0) then (0 : ℂ) else q.cumulantTerm t jr‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' jr, |t * Real.log q.val| * (if jr = (0, 0) then 0 else q.ladderWeight 0 jr) :=
        hnorm.tsum_le_tsum hbound hmaj
    _ = |t * Real.log q.val| * (q.meanSeries - q.val) := by
        rw [tsum_mul_left, RealEulerNome.meanSeries, hWsplit, hW0]
        ring

/-- At the wall, the remainder of one prime is at most `8|θ| log p/(p² log P)`. -/
theorem norm_wallRemainder_le (P : ℕ) (θ : ℝ) (p : Nat.Primes) :
    ‖(∑' jr, (primeNome one_pos p).cumulantTerm (-θ / Real.log P) jr)
        - (primeNome one_pos p).cumulantTerm (-θ / Real.log P) (0, 0)‖
      ≤ 8 * |θ| / |Real.log P| * (Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
  set q := primeNome one_pos p
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hq : q.val = ((p : ℕ) : ℝ)⁻¹ := by
    rw [primeNome_val, Real.rpow_neg_one]
  have hq2 : q.val ≤ 1 / 2 := by
    rw [hq]
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hq0 := q.pos
  have hmean := q.meanSeries_le
  have hsub : q.meanSeries - q.val ≤ 8 * q.val ^ 2 := by
    have hq1 : 1 / 2 ≤ 1 - q.val := by linarith
    have h1 : q.val / (1 - q.val) ^ 2 - q.val ≤ 8 * q.val ^ 2 := by
      rw [div_sub' (by positivity), div_le_iff₀ (by positivity)]
      have h4 : 1 / 4 ≤ (1 - q.val) ^ 2 := by nlinarith
      have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 8 * q.val ^ 2)
      nlinarith [pow_pos hq0 3]
    linarith
  have hmain := q.norm_tsum_cumulantTerm_sub_le (-θ / Real.log P)
  have hlp : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hlogq : |(-θ / Real.log P) * Real.log q.val|
      = |θ| / |Real.log P| * Real.log ((p : ℕ) : ℝ) := by
    have hlp' : |Real.log ((p : ℕ) : ℝ)| = Real.log ((p : ℕ) : ℝ) := abs_of_nonneg hlp
    rw [log_primeNome, one_mul, abs_mul, abs_div, abs_neg, abs_neg, hlp']
  rw [hlogq] at hmain
  refine hmain.trans ?_
  calc |θ| / |Real.log P| * Real.log ((p : ℕ) : ℝ) * (q.meanSeries - q.val)
      ≤ |θ| / |Real.log P| * Real.log ((p : ℕ) : ℝ) * (8 * q.val ^ 2) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = 8 * |θ| / |Real.log P| * (Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
        rw [hq]
        field_simp

theorem sum_primeCutoff_complex (P : ℕ) (f : ℕ → ℂ) :
    ∑ p ∈ primeCutoff P, f (p : ℕ) = ∑ n ∈ Nat.primesLE P, f n := by
  rw [primeCutoff, Finset.sum_map]
  exact Finset.sum_coe_sort (Nat.primesLE P) f

theorem sum_primeCutoff_log_div_sq_le (P : ℕ) :
    ∑ p ∈ primeCutoff P, Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2
      ≤ RHTower.Sieve.logSqTailConst := by
  rw [sum_primeCutoff P (fun n => Real.log (n : ℝ) / (n : ℝ) ^ 2),
    RHTower.Sieve.logSqTailConst]
  refine RHTower.Sieve.summable_log_div_sq.sum_le_tsum _ fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)

/-! ## The Mertens window -/

/-- `G_θ(u) = iθ e^{iθu/2} sinc(θu/2)`, the continuous extension of `(e^{iθu} - 1)/u`. -/
def dickmanQuotient (θ u : ℝ) : ℂ :=
  (θ : ℂ) * I * cexp ((θ * u / 2 : ℝ) * I) * (Real.sinc (θ * u / 2) : ℂ)

theorem continuous_dickmanQuotient (θ : ℝ) : Continuous (dickmanQuotient θ) := by
  unfold dickmanQuotient
  fun_prop

theorem dickmanQuotient_eq (θ : ℝ) {u : ℝ} (hu : u ≠ 0) :
    dickmanQuotient θ u = (cexp ((θ * u : ℝ) * I) - 1) / u := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [dickmanQuotient]
  set x : ℝ := θ * u / 2 with hxdef
  have hx : x ≠ 0 := by rw [hxdef]; positivity
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hsin : (2 : ℂ) * I * (Real.sin x : ℂ) = cexp ((x : ℂ) * I) - cexp (-((x : ℂ) * I)) := by
    rw [Complex.ofReal_sin, Complex.sin, neg_mul]
    have hI : I * I = -1 := I_mul_I
    linear_combination (cexp (-((x : ℂ) * I)) - cexp ((x : ℂ) * I)) * hI
  have hinv : cexp ((x : ℂ) * I) * cexp (-((x : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hsq : cexp ((θ * u : ℝ) * I) = cexp ((x : ℂ) * I) * cexp ((x : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hxdef]
    push_cast
    ring
  have hθx : (θ : ℂ) = 2 * (x : ℂ) / (u : ℂ) := by
    rw [hxdef]
    push_cast
    field_simp
  have hdq : dickmanQuotient θ u = (θ : ℂ) * I * cexp ((x : ℂ) * I) * (Real.sinc x : ℂ) := rfl
  rw [hdq, Real.sinc_of_ne_zero hx, Complex.ofReal_div (Real.sin x) x, hsq, hθx]
  field_simp
  linear_combination (cexp ((x : ℂ) * I)) * hsin - hinv

/-- The Dickman exponent `∫_0^1 (e^{iθu} - 1) du/u`. -/
def dickmanExponent (θ : ℝ) : ℂ := ∫ u in (0 : ℝ)..1, (cexp ((θ * u : ℝ) * I) - 1) / u

theorem dickmanExponent_eq (θ : ℝ) :
    dickmanExponent θ = ∫ u in (0 : ℝ)..1, dickmanQuotient θ u := by
  rw [dickmanExponent]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
  rw [Set.uIoc_of_le zero_le_one] at hu
  exact (dickmanQuotient_eq θ hu.1.ne').symm

theorem norm_dickmanExponent_le (θ : ℝ) : ‖dickmanExponent θ‖ ≤ |θ| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := |θ|)
    (f := fun u : ℝ => (cexp ((θ * u : ℝ) * I) - 1) / u) (fun u hu => ?_)
  · simpa [dickmanExponent] using h
  rw [Set.uIoc_of_le zero_le_one] at hu
  have hu0 : 0 < u := hu.1
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ * u)
  rw [mul_comm I] at hb
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu0.le, div_le_iff₀ hu0]
  refine hb.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hu0]

/-- The main sum `∑_{p ≤ P} (e^{iθ log p/log P} - 1)/p`. -/
def wallMainSum (P : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Nat.primesLE P, (cexp ((θ * (Real.log n / Real.log P) : ℝ) * I) - 1) / (n : ℂ)

theorem wallMainSum_eq_window {P : ℕ} (hP : 2 ≤ P) (θ : ℝ) :
    wallMainSum P θ
      = ((RHTower.mertensPrimeWindow (fun u => (dickmanQuotient θ u).re) P / Real.log P : ℝ) : ℂ)
        + ((RHTower.mertensPrimeWindow (fun u => (dickmanQuotient θ u).im) P
          / Real.log P : ℝ) : ℂ) * I := by
  have hP2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hL : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hL' : ((Real.log P : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hterm : ∀ n ∈ Finset.Icc 0 P,
      (((dickmanQuotient θ (Real.log n / Real.log P)).re
          * RHTower.mertensPrimeWeight n : ℝ) : ℂ)
        + (((dickmanQuotient θ (Real.log n / Real.log P)).im
          * RHTower.mertensPrimeWeight n : ℝ) : ℂ) * I
      = ((Real.log P : ℝ) : ℂ) * (if n.Prime then
          (cexp ((θ * (Real.log n / Real.log P) : ℝ) * I) - 1) / (n : ℂ) else 0) := by
    intro n _
    rw [RHTower.mertensPrimeWeight]
    split_ifs with hn
    · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
      have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have hu : Real.log (n : ℝ) / Real.log P ≠ 0 := by positivity
      have hG := dickmanQuotient_eq θ hu
      have hsplit := Complex.re_add_im (dickmanQuotient θ (Real.log n / Real.log P))
      have hwu : Real.log n / n / (Real.log n / Real.log P) = Real.log P / n := by
        field_simp
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne_zero
      calc (((dickmanQuotient θ (Real.log n / Real.log P)).re * (Real.log n / n) : ℝ) : ℂ)
            + (((dickmanQuotient θ (Real.log n / Real.log P)).im * (Real.log n / n) : ℝ) : ℂ) * I
          = dickmanQuotient θ (Real.log n / Real.log P) * ((Real.log n / n : ℝ) : ℂ) := by
            rw [Complex.ofReal_mul, Complex.ofReal_mul]
            linear_combination ((Real.log n / n : ℝ) : ℂ) * hsplit
        _ = (cexp ((θ * (Real.log n / Real.log P) : ℝ) * I) - 1)
              * ((Real.log n / n / (Real.log n / Real.log P) : ℝ) : ℂ) := by
            rw [hG, Complex.ofReal_div (Real.log n / n)]
            ring
        _ = ((Real.log P : ℝ) : ℂ)
              * ((cexp ((θ * (Real.log n / Real.log P) : ℝ) * I) - 1) / (n : ℂ)) := by
            rw [hwu, Complex.ofReal_div, Complex.ofReal_natCast]
            ring
    · simp
  have hcomb : ((RHTower.mertensPrimeWindow (fun u => (dickmanQuotient θ u).re) P : ℝ) : ℂ)
      + ((RHTower.mertensPrimeWindow (fun u => (dickmanQuotient θ u).im) P : ℝ) : ℂ) * I
      = ((Real.log P : ℝ) : ℂ) * wallMainSum P θ := by
    rw [RHTower.mertensPrimeWindow, RHTower.mertensPrimeWindow, Complex.ofReal_sum,
      Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm,
      ← Finset.mul_sum, wallMainSum, Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
  rw [← mul_div_cancel_left₀ (wallMainSum P θ) hL', ← hcomb, Complex.ofReal_div,
    Complex.ofReal_div]
  ring

/-- **The Mertens window of the Dickman quotient.** -/
theorem tendsto_wallMainSum (θ : ℝ) :
    Tendsto (fun P : ℕ => wallMainSum P θ) atTop (𝓝 (dickmanExponent θ)) := by
  have hc := continuous_dickmanQuotient θ
  have h1 := RHTower.tendsto_mertensPrimeWindow_div_log
    (g := fun u => (dickmanQuotient θ u).re) (Complex.continuous_re.comp hc).continuousOn
  have h2 := RHTower.tendsto_mertensPrimeWindow_div_log
    (g := fun u => (dickmanQuotient θ u).im) (Complex.continuous_im.comp hc).continuousOn
  have hlim := ((Complex.continuous_ofReal.tendsto _).comp h1).add
    (((Complex.continuous_ofReal.tendsto _).comp h2).mul_const I)
  have hint : dickmanExponent θ = ((∫ u in (0 : ℝ)..1, (dickmanQuotient θ u).re : ℝ) : ℂ)
      + ((∫ u in (0 : ℝ)..1, (dickmanQuotient θ u).im : ℝ) : ℂ) * I := by
    rw [dickmanExponent_eq, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
      ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun u _ => (Complex.re_add_im _).symm
    · exact (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hc)).intervalIntegrable _ _
    · exact ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp hc)).mul
        continuous_const).intervalIntegrable _ _
  rw [hint]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with P hP
  exact (wallMainSum_eq_window hP θ).symm

/-! ## Convergence of the wall law -/

theorem wallExponent_sub_mainSum_norm_le (P : ℕ) (θ : ℝ) :
    ‖wallExponent P θ - wallMainSum P θ‖
      ≤ 8 * |θ| / |Real.log P| * RHTower.Sieve.logSqTailConst := by
  have hmain : wallMainSum P θ
      = ∑ p ∈ primeCutoff P, (primeNome one_pos p).cumulantTerm (-θ / Real.log P) (0, 0) := by
    rw [wallMainSum, ← sum_primeCutoff_complex P
      (fun n => (cexp ((θ * (Real.log n / Real.log P) : ℝ) * I) - 1) / (n : ℂ))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [RealEulerNome.cumulantTerm_zero, log_primeNome, primeNome_val, Real.rpow_neg_one]
    have harg : ((-θ / Real.log P * -(1 * Real.log ((p : ℕ) : ℝ)) : ℝ) : ℂ)
        = ((θ * (Real.log ((p : ℕ) : ℝ) / Real.log P) : ℝ) : ℂ) := by
      congr 1
      ring
    rw [harg, Complex.ofReal_inv, Complex.ofReal_natCast]
    ring
  rw [wallExponent, hmain, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p ∈ primeCutoff P, ‖(∑' jr, (primeNome one_pos p).cumulantTerm (-θ / Real.log P) jr)
          - (primeNome one_pos p).cumulantTerm (-θ / Real.log P) (0, 0)‖
      ≤ ∑ p ∈ primeCutoff P, 8 * |θ| / |Real.log P|
          * (Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) :=
        Finset.sum_le_sum fun p _ => norm_wallRemainder_le P θ p
    _ = 8 * |θ| / |Real.log P| * ∑ p ∈ primeCutoff P,
          Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_primeCutoff_log_div_sq_le P) (by positivity)

theorem tendsto_wallExponent (θ : ℝ) :
    Tendsto (fun P : ℕ => wallExponent P θ) atTop (𝓝 (dickmanExponent θ)) := by
  have hrem : Tendsto (fun P : ℕ => wallExponent P θ - wallMainSum P θ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlog : Tendsto (fun P : ℕ => |Real.log (P : ℝ)|) atTop atTop :=
      tendsto_abs_atTop_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hmaj : Tendsto (fun P : ℕ => 8 * |θ| / |Real.log (P : ℝ)| * RHTower.Sieve.logSqTailConst)
        atTop (𝓝 0) := by
      have h := (hlog.inv_tendsto_atTop.const_mul (8 * |θ|)).mul_const
        RHTower.Sieve.logSqTailConst
      simpa [div_eq_mul_inv] using h
    exact squeeze_zero (fun _ => norm_nonneg _) (fun P => wallExponent_sub_mainSum_norm_le P θ)
      hmaj
  have h := hrem.add (tendsto_wallMainSum θ)
  simpa using h

theorem continuousAt_exp_dickmanExponent :
    ContinuousAt (fun θ : ℝ => cexp (dickmanExponent θ)) 0 := by
  have h0 : dickmanExponent 0 = 0 := by
    have := norm_dickmanExponent_le 0
    simpa using this
  have hI : Tendsto dickmanExponent (𝓝 0) (𝓝 (dickmanExponent 0)) := by
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun θ => norm_dickmanExponent_le θ) ?_
    have := (continuous_abs.tendsto (0 : ℝ))
    simpa using this
  exact (Complex.continuous_exp.tendsto _).comp hI

/-- **The Dickman law exists.**  There is a probability measure with
`log E e^{iθD} = ∫_0^1 (e^{iθu} - 1) du/u`, and `W_P` converges to it in law. -/
theorem exists_dickmanLaw :
    ∃ D : ProbabilityMeasure ℝ, (∀ θ, charFun (D : Measure ℝ) θ = cexp (dickmanExponent θ)) ∧
      Tendsto wallLaw atTop (𝓝 D) :=
  exists_tendsto_of_tendsto_charFun continuousAt_exp_dickmanExponent fun θ => by
    simp_rw [charFun_wallLaw]
    exact (Complex.continuous_exp.tendsto _).comp (tendsto_wallExponent θ)

/-- The Dickman law `D` with `log E e^{iθD} = ∫_0^1 (e^{iθu} - 1) du/u`. -/
def dickmanLaw : ProbabilityMeasure ℝ := Classical.choose exists_dickmanLaw

theorem charFun_dickmanLaw (θ : ℝ) :
    charFun (dickmanLaw : Measure ℝ) θ = cexp (dickmanExponent θ) :=
  (Classical.choose_spec exists_dickmanLaw).1 θ

/-- **Theorem 3.2 (GAS3.6).**  At the wall `σ = 1`, `W_P ⇒ D`. -/
theorem tendsto_wallLaw_dickmanLaw : Tendsto wallLaw atTop (𝓝 dickmanLaw) :=
  (Classical.choose_spec exists_dickmanLaw).2

/-- The Dickman law is determined by its characteristic function. -/
theorem dickmanLaw_unique {D : ProbabilityMeasure ℝ}
    (hD : ∀ θ, charFun (D : Measure ℝ) θ = cexp (dickmanExponent θ)) : D = dickmanLaw := by
  have h : (D : Measure ℝ) = (dickmanLaw : Measure ℝ) := by
    apply Measure.ext_of_charFun
    funext θ
    rw [hD, charFun_dickmanLaw]
  exact Subtype.ext h

end GaloisForLFunctions.HTGeometry
