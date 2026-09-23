import GaloisForLFunctions.HTGeometry.BohrSpectrum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The almost-periodic algebra, orthonormal characters, and Bessel's inequality

The mean value turns the continuous almost-periodic functions into a pre-Hilbert space: `⟪f, g⟫ =
M(f · conj g)`.  This file proves that the class is closed under the vector-space and ring
operations, that the mean is linear and conjugation-equivariant, that the characters
`e_λ(t) = e^{iλt}` form an orthonormal system for the mean, and Bessel's inequality

`∑_{λ ∈ S} |a(λ)|² ≤ M(|f|²)`

for every finite set `S` of frequencies.  Bessel is the first structural constraint on the Bohr
spectrum: only finitely many frequencies carry a coefficient above any positive threshold, so the
spectrum is a countable union of finite sets.
-/

open Filter Topology MeasureTheory ComplexConjugate

namespace GaloisForLFunctions

open HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-! ### Closure properties of the almost-periodic class -/

/-- Sums of almost-periodic functions are almost periodic (via their common almost periods). -/
theorem isBohrAlmostPeriodic_add {f g : ℝ → E} (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : IsBohrAlmostPeriodic g) :
    IsBohrAlmostPeriodic (fun t => f t + g t) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ :=
    exists_common_almostPeriods hfc hfa hgc hga (ε := ε / 2) (by linarith)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτf, hτg⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  calc ‖(f (x + τ) + g (x + τ)) - (f x + g x)‖
      = ‖(f (x + τ) - f x) + (g (x + τ) - g x)‖ := by congr 1; abel
    _ ≤ ‖f (x + τ) - f x‖ + ‖g (x + τ) - g x‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hτf x) (hτg x)
    _ = ε := by ring

/-- Negation preserves almost periodicity. -/
theorem isBohrAlmostPeriodic_neg {f : ℝ → E} (hfa : IsBohrAlmostPeriodic f) :
    IsBohrAlmostPeriodic (fun t => -f t) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hfa ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  rw [show -f (x + τ) - -f x = -(f (x + τ) - f x) by abel, norm_neg]
  exact hτ x

/-- Differences of almost-periodic functions are almost periodic. -/
theorem isBohrAlmostPeriodic_sub {f g : ℝ → E} (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : IsBohrAlmostPeriodic g) :
    IsBohrAlmostPeriodic (fun t => f t - g t) := by
  have h := isBohrAlmostPeriodic_add hfc hfa hgc.neg (isBohrAlmostPeriodic_neg hga)
  simpa [sub_eq_add_neg] using h

/-- Complex scalar multiples of almost-periodic functions are almost periodic. -/
theorem isBohrAlmostPeriodic_const_mul (c : ℂ) {f : ℝ → ℂ} (hfa : IsBohrAlmostPeriodic f) :
    IsBohrAlmostPeriodic (fun t => c * f t) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simpa using isBohrAlmostPeriodic_const (0 : ℂ)
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hfa (ε / ‖c‖) (by positivity)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [show c * f (x + τ) - c * f x = c * (f (x + τ) - f x) by ring, norm_mul]
  calc ‖c‖ * ‖f (x + τ) - f x‖ ≤ ‖c‖ * (ε / ‖c‖) :=
        mul_le_mul_of_nonneg_left (hτ x) (norm_nonneg _)
    _ = ε := by field_simp

/-- Complex conjugation preserves almost periodicity. -/
theorem isBohrAlmostPeriodic_conj {f : ℝ → ℂ} (hfa : IsBohrAlmostPeriodic f) :
    IsBohrAlmostPeriodic (fun t => conj (f t)) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hfa ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  rw [← map_sub, Complex.norm_conj]
  exact hτ x

/-- Finite sums of almost-periodic functions are almost periodic. -/
theorem isBohrAlmostPeriodic_sum {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℂ}
    (hc : ∀ i ∈ S, Continuous (F i)) (ha : ∀ i ∈ S, IsBohrAlmostPeriodic (F i)) :
    IsBohrAlmostPeriodic (fun t => ∑ i ∈ S, F i t) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using isBohrAlmostPeriodic_const (0 : ℂ)
  | insert j S hj ih =>
      have hcj : Continuous (F j) := hc j (Finset.mem_insert_self j S)
      have haj : IsBohrAlmostPeriodic (F j) := ha j (Finset.mem_insert_self j S)
      have hcS : ∀ i ∈ S, Continuous (F i) := fun i hi => hc i (Finset.mem_insert_of_mem hi)
      have haS : ∀ i ∈ S, IsBohrAlmostPeriodic (F i) := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hsumC : Continuous fun t => ∑ i ∈ S, F i t := continuous_finsetSum S hcS
      have hstep : (fun t => ∑ i ∈ insert j S, F i t) = fun t => F j t + ∑ i ∈ S, F i t := by
        funext t
        rw [Finset.sum_insert hj]
      rw [hstep]
      exact isBohrAlmostPeriodic_add hcj haj hsumC (ih hcS haS)

/-! ### Linearity of the window average and of the mean -/

theorem windowAverage_add {f g : ℝ → ℂ} (hfc : Continuous f) (hgc : Continuous g) (T : ℝ) :
    windowAverage (fun t => f t + g t) T = windowAverage f T + windowAverage g T := by
  simp only [windowAverage]
  rw [intervalIntegral.integral_add (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _),
    smul_add]

theorem windowAverage_const_mul (c : ℂ) (f : ℝ → ℂ) (T : ℝ) :
    windowAverage (fun t => c * f t) T = c * windowAverage f T := by
  simp only [windowAverage]
  rw [show (fun t => c * f t) = fun t => c • f t from rfl, intervalIntegral.integral_smul,
    smul_comm]
  simp

theorem windowAverage_conj (f : ℝ → ℂ) (T : ℝ) :
    windowAverage (fun t => conj (f t)) T = conj (windowAverage f T) := by
  simp only [windowAverage]
  rw [intervalIntegral.intervalIntegral_conj]
  simp [Complex.real_smul]

theorem bohrMean_zero : bohrMean (fun _ : ℝ => (0 : ℂ)) = 0 := by
  refine bohrMean_eq continuous_const (isBohrAlmostPeriodic_const 0) ?_
  have hw : windowAverage (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
    funext T
    simp [windowAverage]
  rw [hw]
  exact tendsto_const_nhds

theorem bohrMean_add {f g : ℝ → ℂ} (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : IsBohrAlmostPeriodic g) :
    bohrMean (fun t => f t + g t) = bohrMean f + bohrMean g := by
  refine bohrMean_eq (hfc.add hgc) (isBohrAlmostPeriodic_add hfc hfa hgc hga) ?_
  refine ((tendsto_windowAverage_bohrMean hfc hfa).add
    (tendsto_windowAverage_bohrMean hgc hga)).congr (fun T => ?_)
  exact (windowAverage_add hfc hgc T).symm

theorem bohrMean_const_mul (c : ℂ) {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : IsBohrAlmostPeriodic f) :
    bohrMean (fun t => c * f t) = c * bohrMean f := by
  refine bohrMean_eq (continuous_const.mul hfc) (isBohrAlmostPeriodic_const_mul c hfa) ?_
  refine ((tendsto_windowAverage_bohrMean hfc hfa).const_mul c).congr (fun T => ?_)
  exact (windowAverage_const_mul c f T).symm

theorem bohrMean_conj {f : ℝ → ℂ} (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f) :
    bohrMean (fun t => conj (f t)) = conj (bohrMean f) := by
  refine bohrMean_eq (Complex.continuous_conj.comp hfc) (isBohrAlmostPeriodic_conj hfa) ?_
  refine ((Complex.continuous_conj.tendsto (bohrMean f)).comp
    (tendsto_windowAverage_bohrMean hfc hfa)).congr (fun T => ?_)
  exact (windowAverage_conj f T).symm

theorem bohrMean_sub {f g : ℝ → ℂ} (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : IsBohrAlmostPeriodic g) :
    bohrMean (fun t => f t - g t) = bohrMean f - bohrMean g := by
  have hneg : bohrMean (fun t => -g t) = -bohrMean g := by
    have h := bohrMean_const_mul (-1 : ℂ) hgc hga
    simpa using h
  have hadd := bohrMean_add hfc hfa hgc.neg (isBohrAlmostPeriodic_neg hga)
  calc bohrMean (fun t => f t - g t)
      = bohrMean (fun t => f t + -g t) := by simp only [sub_eq_add_neg]
    _ = bohrMean f + bohrMean (fun t => -g t) := hadd
    _ = bohrMean f - bohrMean g := by rw [hneg]; ring

theorem bohrMean_sum {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℂ}
    (hc : ∀ i ∈ S, Continuous (F i)) (ha : ∀ i ∈ S, IsBohrAlmostPeriodic (F i)) :
    bohrMean (fun t => ∑ i ∈ S, F i t) = ∑ i ∈ S, bohrMean (F i) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using bohrMean_zero
  | insert j S hj ih =>
      have hcj : Continuous (F j) := hc j (Finset.mem_insert_self j S)
      have haj : IsBohrAlmostPeriodic (F j) := ha j (Finset.mem_insert_self j S)
      have hcS : ∀ i ∈ S, Continuous (F i) := fun i hi => hc i (Finset.mem_insert_of_mem hi)
      have haS : ∀ i ∈ S, IsBohrAlmostPeriodic (F i) := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hsumC : Continuous fun t => ∑ i ∈ S, F i t := continuous_finsetSum S hcS
      have hsumA : IsBohrAlmostPeriodic fun t => ∑ i ∈ S, F i t :=
        isBohrAlmostPeriodic_sum S hcS haS
      have hstep : (fun t => ∑ i ∈ insert j S, F i t)
          = fun t => F j t + ∑ i ∈ S, F i t := by
        funext t
        rw [Finset.sum_insert hj]
      rw [hstep, bohrMean_add hcj haj hsumC hsumA, ih hcS haS, Finset.sum_insert hj]

/-! ### The characters are orthonormal for the mean -/

/-- The character `t ↦ e^{iλt}`, conjugate to `bohrChar`. -/
noncomputable def bohrExp (lam : ℝ) : ℝ → ℂ := bohrChar (-lam)

theorem continuous_bohrExp (lam : ℝ) : Continuous (bohrExp lam) := continuous_bohrChar _

theorem isBohrAlmostPeriodic_bohrExp (lam : ℝ) : IsBohrAlmostPeriodic (bohrExp lam) :=
  isBohrAlmostPeriodic_bohrChar _

theorem conj_bohrExp (lam t : ℝ) : conj (bohrExp lam t) = bohrChar lam t := by
  simp only [bohrExp, bohrChar, ← Complex.exp_conj]
  congr 1
  simp

theorem bohrChar_mul (lam mu t : ℝ) :
    bohrChar lam t * bohrChar mu t = bohrChar (lam + mu) t := by
  simp only [bohrChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem bohrExp_mul_bohrChar (lam mu t : ℝ) :
    bohrExp lam t * bohrChar mu t = bohrChar (mu - lam) t := by
  rw [bohrExp, bohrChar_mul]
  congr 1
  ring

/-- The mean of a nontrivial character vanishes; the trivial character has mean `1`. -/
theorem bohrMean_bohrChar (lam : ℝ) :
    bohrMean (bohrChar lam) = if lam = 0 then 1 else 0 := by
  rcases eq_or_ne lam 0 with hlam | hlam
  · subst hlam
    rw [if_pos rfl]
    refine bohrMean_eq (continuous_bohrChar 0) (isBohrAlmostPeriodic_bohrChar 0) ?_
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hchar : bohrChar 0 = fun _ : ℝ => (1 : ℂ) := by
      funext t; simp [bohrChar]
    symm
    simp only [windowAverage, hchar]
    rw [intervalIntegral.integral_const, sub_zero, smul_smul, inv_mul_cancel₀ hT.ne', one_smul]
  · rw [if_neg hlam]
    refine bohrMean_eq (continuous_bohrChar lam) (isBohrAlmostPeriodic_bohrChar lam) ?_
    set c : ℂ := -(lam : ℂ) * Complex.I with hc
    have hcne : c ≠ 0 := by
      simp only [hc]
      exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hlam)) Complex.I_ne_zero
    have hcnorm : ‖c‖ = |lam| := by
      simp [hc]
    have hchar : ∀ t : ℝ, bohrChar lam t = Complex.exp (c * (t : ℂ)) := by
      intro t
      simp only [bohrChar, hc]
      congr 1
      push_cast
      ring
    have hint : ∀ T : ℝ, (∫ t in (0 : ℝ)..T, bohrChar lam t)
        = (Complex.exp (c * (T : ℂ)) - 1) / c := by
      intro T
      rw [show (fun t : ℝ => bohrChar lam t) = fun t : ℝ => Complex.exp (c * (t : ℂ)) from
        funext hchar]
      rw [integral_exp_mul_complex hcne]
      simp
    have hbound : ∀ T : ℝ, 0 < T → ‖windowAverage (bohrChar lam) T‖ ≤ 2 / (|lam| * T) := by
      intro T hT
      have habs : 0 < |lam| := abs_pos.mpr hlam
      have hnum : ‖Complex.exp (c * (T : ℂ)) - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        have h1 : ‖Complex.exp (c * (T : ℂ))‖ = 1 := by
          rw [Complex.norm_exp]
          have hre : (c * (T : ℂ)).re = 0 := by simp [hc]
          rw [hre, Real.exp_zero]
        rw [h1, norm_one]
        norm_num
      simp only [windowAverage]
      rw [hint T, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ T⁻¹), norm_div, hcnorm]
      have hrw : T⁻¹ * (‖Complex.exp (c * (T : ℂ)) - 1‖ / |lam|)
          = ‖Complex.exp (c * (T : ℂ)) - 1‖ / (|lam| * T) := by
        field_simp
      rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hnum, mul_pos habs hT]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun T : ℝ => 2 / (|lam| * T))
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact hbound T hT
    · have habs : 0 < |lam| := abs_pos.mpr hlam
      have : Tendsto (fun T : ℝ => |lam| * T) atTop atTop :=
        Filter.Tendsto.const_mul_atTop habs tendsto_id
      exact tendsto_const_nhds.div_atTop this

/-- Orthonormality of the characters for the Bohr mean. -/
theorem bohrMean_bohrExp_mul_conj (lam mu : ℝ) :
    bohrMean (fun t => bohrExp lam t * conj (bohrExp mu t)) = if lam = mu then 1 else 0 := by
  have hfun : (fun t => bohrExp lam t * conj (bohrExp mu t)) = bohrChar (mu - lam) := by
    funext t
    rw [conj_bohrExp, bohrExp_mul_bohrChar]
  rw [hfun, bohrMean_bohrChar]
  by_cases h : lam = mu
  · rw [if_pos (by rw [h]; ring), if_pos h]
  · rw [if_neg (by intro hz; exact h (by linarith [sub_eq_zero.mp hz])), if_neg h]



/-! ### Bessel's inequality -/

theorem windowAverage_sub {f g : ℝ → ℂ} (hfc : Continuous f) (hgc : Continuous g) (T : ℝ) :
    windowAverage (fun t => f t - g t) T = windowAverage f T - windowAverage g T := by
  simp only [windowAverage]
  rw [intervalIntegral.integral_sub (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _),
    smul_sub]

/-- The mean of `|h|²` is a nonnegative real. -/
theorem bohrMean_mul_conj_re_nonneg {h : ℝ → ℂ} (hhc : Continuous h)
    (hha : IsBohrAlmostPeriodic h) :
    0 ≤ (bohrMean (fun t => h t * conj (h t))).re := by
  have hconjc : Continuous fun t => conj (h t) := Complex.continuous_conj.comp hhc
  have hprodc : Continuous fun t => h t * conj (h t) := hhc.mul hconjc
  have hproda : IsBohrAlmostPeriodic fun t => h t * conj (h t) :=
    isBohrAlmostPeriodic_mul hhc hha hconjc (isBohrAlmostPeriodic_conj hha)
  have hlim := tendsto_windowAverage_bohrMean hprodc hproda
  have hre : Tendsto (fun T => (windowAverage (fun t => h t * conj (h t)) T).re) atTop
      (nhds (bohrMean (fun t => h t * conj (h t))).re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  refine ge_of_tendsto hre ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hval : (fun t => h t * conj (h t)) = fun t => ((‖h t‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    funext t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..T, ‖h t‖ ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hT.le (fun u _ => by positivity)
  simp only [windowAverage, hval, intervalIntegral.integral_ofReal, Complex.real_smul]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

/-- The Bohr coefficient of a character. -/
theorem bohrCoefficient_bohrExp (mu lam : ℝ) :
    bohrCoefficient (bohrExp mu) lam = if lam = mu then 1 else 0 := by
  have hfun : (fun t => bohrExp mu t * bohrChar lam t) = bohrChar (lam - mu) := by
    funext t
    exact bohrExp_mul_bohrChar mu lam t
  rw [bohrCoefficient, hfun, bohrMean_bohrChar]
  by_cases h : lam = mu
  · rw [if_pos (by rw [h]; ring), if_pos h]
  · rw [if_neg (fun hz => h (by linarith [sub_eq_zero.mp hz])), if_neg h]

/-- **Bessel's inequality.**  The squared Bohr coefficients over any finite set of frequencies are
dominated by the mean of `|f|²`. -/
theorem bohr_bessel {f : ℝ → ℂ} (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f) (S : Finset ℝ) :
    ∑ i ∈ S, ‖bohrCoefficient f i‖ ^ (2 : ℕ) ≤ (bohrMean (fun t => f t * conj (f t))).re := by
  classical
  set a : ℝ → ℂ := bohrCoefficient f with hadef
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ → ℂ, ∀ t, p t = ∑ i ∈ S, a i * bohrExp i t :=
    ⟨fun t => ∑ i ∈ S, a i * bohrExp i t, fun _ => rfl⟩
  have hterm_c : ∀ i : ℝ, Continuous fun t => a i * bohrExp i t :=
    fun i => continuous_const.mul (continuous_bohrExp i)
  have hterm_a : ∀ i : ℝ, IsBohrAlmostPeriodic fun t => a i * bohrExp i t :=
    fun i => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrExp i)
  have hpc : Continuous p := by
    have : Continuous fun t => ∑ i ∈ S, a i * bohrExp i t :=
      continuous_finsetSum S fun i _ => hterm_c i
    exact this.congr fun t => (hpdef t).symm
  have hpa : IsBohrAlmostPeriodic p := by
    have h := isBohrAlmostPeriodic_sum S (fun i _ => hterm_c i) (fun i _ => hterm_a i)
    intro ε hε
    obtain ⟨L, hL, hd⟩ := h ε hε
    refine ⟨L, hL, fun c => ?_⟩
    obtain ⟨τ, hτm, hτ⟩ := hd c
    exact ⟨τ, hτm, fun x => by rw [hpdef, hpdef]; exact hτ x⟩
  have hconjpc : Continuous fun t => conj (p t) := Complex.continuous_conj.comp hpc
  have hconjfc : Continuous fun t => conj (f t) := Complex.continuous_conj.comp hfc
  have hconjpa : IsBohrAlmostPeriodic fun t => conj (p t) := isBohrAlmostPeriodic_conj hpa
  have hconjfa : IsBohrAlmostPeriodic fun t => conj (f t) := isBohrAlmostPeriodic_conj hfa
  -- the Bohr coefficients of the trigonometric polynomial
  have hcoefp : ∀ i ∈ S, bohrCoefficient p i = a i := by
    intro i hi
    have hpi : (fun t => p t * bohrChar i t)
        = fun t => ∑ j ∈ S, a j * (bohrExp j t * bohrChar i t) := by
      funext t
      rw [hpdef t, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hsum : bohrMean (fun t => ∑ j ∈ S, a j * (bohrExp j t * bohrChar i t))
        = ∑ j ∈ S, bohrMean (fun t => a j * (bohrExp j t * bohrChar i t)) := by
      refine bohrMean_sum (F := fun j => fun t => a j * (bohrExp j t * bohrChar i t)) S
        (fun j _ => ?_) (fun j _ => ?_)
      · exact continuous_const.mul ((continuous_bohrExp j).mul (continuous_bohrChar i))
      · exact isBohrAlmostPeriodic_const_mul _
          (isBohrAlmostPeriodic_mul (continuous_bohrExp j) (isBohrAlmostPeriodic_bohrExp j)
            (continuous_bohrChar i) (isBohrAlmostPeriodic_bohrChar i))
    have hval : ∀ j ∈ S, bohrMean (fun t => a j * (bohrExp j t * bohrChar i t))
        = if j = i then a j else 0 := by
      intro j _
      rw [bohrMean_const_mul (f := fun t => bohrExp j t * bohrChar i t) _
        ((continuous_bohrExp j).mul (continuous_bohrChar i))
        (isBohrAlmostPeriodic_mul (continuous_bohrExp j) (isBohrAlmostPeriodic_bohrExp j)
          (continuous_bohrChar i) (isBohrAlmostPeriodic_bohrChar i))]
      have hfun : (fun t => bohrExp j t * bohrChar i t) = bohrChar (i - j) := by
        funext t
        exact bohrExp_mul_bohrChar j i t
      rw [hfun, bohrMean_bohrChar]
      by_cases h : j = i
      · rw [if_pos (by rw [h]; ring), if_pos h, mul_one]
      · rw [if_neg (fun hz => h (by linarith [sub_eq_zero.mp hz])), if_neg h, mul_zero]
    rw [bohrCoefficient, hpi, hsum, Finset.sum_congr rfl hval, Finset.sum_ite_eq' S i a,
      if_pos hi]
  -- the three mixed means
  have hMfp : bohrMean (fun t => f t * conj (p t)) = ∑ i ∈ S, conj (a i) * a i := by
    have hfp : (fun t => f t * conj (p t))
        = fun t => ∑ i ∈ S, conj (a i) * (f t * bohrChar i t) := by
      funext t
      rw [hpdef t, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, conj_bohrExp]
      ring
    rw [hfp]
    rw [bohrMean_sum (F := fun i => fun t => conj (a i) * (f t * bohrChar i t)) S
      (fun i _ => continuous_const.mul (hfc.mul (continuous_bohrChar i)))
      (fun i _ => isBohrAlmostPeriodic_const_mul _
        (isBohrAlmostPeriodic_mul_bohrChar hfc hfa i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bohrMean_const_mul (f := fun t => f t * bohrChar i t) _ (hfc.mul (continuous_bohrChar i))
      (isBohrAlmostPeriodic_mul_bohrChar hfc hfa i)]
    simp only [hadef, bohrCoefficient]
  have hMpf : bohrMean (fun t => p t * conj (f t)) = ∑ i ∈ S, a i * conj (a i) := by
    have hconjfun : (fun t => conj (f t * conj (p t))) = fun t => p t * conj (f t) := by
      funext t
      rw [map_mul, Complex.conj_conj]
      ring
    have h := bohrMean_conj (f := fun t => f t * conj (p t)) (hfc.mul hconjpc)
      (isBohrAlmostPeriodic_mul hfc hfa hconjpc hconjpa)
    rw [hconjfun, hMfp] at h
    rw [h, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj]
  have hMpp : bohrMean (fun t => p t * conj (p t)) = ∑ i ∈ S, a i * conj (a i) := by
    have hpp : (fun t => p t * conj (p t))
        = fun t => ∑ i ∈ S, a i * (bohrExp i t * conj (p t)) := by
      funext t
      nth_rewrite 1 [hpdef t]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hpp]
    rw [bohrMean_sum (F := fun i => fun t => a i * (bohrExp i t * conj (p t))) S
      (fun i _ => continuous_const.mul ((continuous_bohrExp i).mul hconjpc))
      (fun i _ => isBohrAlmostPeriodic_const_mul _
        (isBohrAlmostPeriodic_mul (continuous_bohrExp i) (isBohrAlmostPeriodic_bohrExp i)
          hconjpc hconjpa))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [bohrMean_const_mul (f := fun t => bohrExp i t * conj (p t)) _
      ((continuous_bohrExp i).mul hconjpc)
      (isBohrAlmostPeriodic_mul (continuous_bohrExp i) (isBohrAlmostPeriodic_bohrExp i)
        hconjpc hconjpa)]
    congr 1
    have hconjfun : (fun t => conj (bohrExp i t * conj (p t))) = fun t => p t * bohrChar i t := by
      funext t
      rw [map_mul, Complex.conj_conj, conj_bohrExp]
      ring
    have h := bohrMean_conj (f := fun t => bohrExp i t * conj (p t))
      ((continuous_bohrExp i).mul hconjpc)
      (isBohrAlmostPeriodic_mul (continuous_bohrExp i) (isBohrAlmostPeriodic_bohrExp i)
        hconjpc hconjpa)
    rw [hconjfun] at h
    have hc := hcoefp i hi
    rw [bohrCoefficient] at hc
    rw [hc] at h
    exact (Complex.conj_conj (bohrMean fun t => bohrExp i t * conj (p t))) ▸ congrArg conj h.symm
  -- expansion of the mean of `|f - p|²`
  have hexpand : (fun t => (f t - p t) * conj (f t - p t))
      = fun t => f t * conj (f t) - f t * conj (p t) - p t * conj (f t) + p t * conj (p t) := by
    funext t
    rw [map_sub]
    ring
  have hwin : ∀ T : ℝ, windowAverage (fun t => (f t - p t) * conj (f t - p t)) T
      = windowAverage (fun t => f t * conj (f t)) T
        - windowAverage (fun t => f t * conj (p t)) T
        - windowAverage (fun t => p t * conj (f t)) T
        + windowAverage (fun t => p t * conj (p t)) T := by
    intro T
    rw [hexpand]
    rw [windowAverage_add
      (f := fun t => f t * conj (f t) - f t * conj (p t) - p t * conj (f t))
      (g := fun t => p t * conj (p t))
      (((hfc.mul hconjfc).sub (hfc.mul hconjpc)).sub (hpc.mul hconjfc)) (hpc.mul hconjpc),
      windowAverage_sub
      (f := fun t => f t * conj (f t) - f t * conj (p t))
      (g := fun t => p t * conj (f t))
      ((hfc.mul hconjfc).sub (hfc.mul hconjpc)) (hpc.mul hconjfc),
      windowAverage_sub (f := fun t => f t * conj (f t)) (g := fun t => f t * conj (p t))
      (hfc.mul hconjfc) (hfc.mul hconjpc)]
  have hMdiff : bohrMean (fun t => (f t - p t) * conj (f t - p t))
      = bohrMean (fun t => f t * conj (f t)) - bohrMean (fun t => f t * conj (p t))
        - bohrMean (fun t => p t * conj (f t)) + bohrMean (fun t => p t * conj (p t)) := by
    refine bohrMean_eq ((hfc.sub hpc).mul (Complex.continuous_conj.comp (hfc.sub hpc)))
      (isBohrAlmostPeriodic_mul (hfc.sub hpc) (isBohrAlmostPeriodic_sub hfc hfa hpc hpa)
        (Complex.continuous_conj.comp (hfc.sub hpc))
        (isBohrAlmostPeriodic_conj (isBohrAlmostPeriodic_sub hfc hfa hpc hpa))) ?_
    have h1 := tendsto_windowAverage_bohrMean (hfc.mul hconjfc)
      (isBohrAlmostPeriodic_mul hfc hfa hconjfc hconjfa)
    have h2 := tendsto_windowAverage_bohrMean (hfc.mul hconjpc)
      (isBohrAlmostPeriodic_mul hfc hfa hconjpc hconjpa)
    have h3 := tendsto_windowAverage_bohrMean (hpc.mul hconjfc)
      (isBohrAlmostPeriodic_mul hpc hpa hconjfc hconjfa)
    have h4 := tendsto_windowAverage_bohrMean (hpc.mul hconjpc)
      (isBohrAlmostPeriodic_mul hpc hpa hconjpc hconjpa)
    exact (((h1.sub h2).sub h3).add h4).congr fun T => (hwin T).symm
  have hnn := bohrMean_mul_conj_re_nonneg (h := fun t => f t - p t) (hfc.sub hpc)
    (isBohrAlmostPeriodic_sub hfc hfa hpc hpa)
  rw [hMdiff, hMfp, hMpf, hMpp] at hnn
  have hreal : ∀ i : ℝ, conj (a i) * a i = ((‖a i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro i
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hreal' : ∀ i : ℝ, a i * conj (a i) = ((‖a i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro i
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun i _ => hreal i), Finset.sum_congr rfl (fun i _ => hreal' i),
    ← Complex.ofReal_sum] at hnn
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hnn
  linarith

end GaloisForLFunctions
