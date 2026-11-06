import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.HeckeCutoffShifts
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ResonantHeckePoissonMixtureAndDispersion

/-!
# Physical mixed Hecke moments of a resonant state

Let `t_Y = Λ^Y E_u` be a truncated resonant state, `msA u = 0`, `Re u < 0`, and `T_p` the physical
Hecke operator on functions of `(x, y)`.  For words `w, w'` in the primes and `Y ≥ Π w, Π w'`,

`⟨T_w t_Y, T_{w'} t_Y⟩_𝒟 = ‖t_Y‖² ∫ P_{−Re u}(t − Im u) W_w(t) W_{w'}(t) dt`,

with `W_w(t) = Π_{p∈w} 2 cos(t log p)`, the tempered eigenvalue of `T_w`
(`integral_heckeWord_mul_conj_heckeWord`).  So the whole Hecke algebra, across all primes and with
repeated primes, has the Poisson kernel at `u` as its joint spectral measure on the physical state.
For a squarefree product `n` this reads `⟨T_w t_Y, t_Y⟩ = μ_n(u) ‖t_Y‖²`, the formal all-`n` moment
(`integral_heckeWord_mul_conj_eq_resonantHeckeMoment`).

**Mechanism.**  On the resonant cutoff family `S(x) = e^{ux} t_{Ye^x}`, each `T_p` is the sum of the two
translations `x ↦ x ± log p` (`hecke_cutoff_shifts`).  The cutoff Gram kernel makes `S` a stationary
process: `⟨S(x), S(x')⟩ = ‖t_Y‖² e^{−σ|x−x'| + i t₀ (x−x')}`, with `u = −σ + i t₀`, and this covariance is
the Fourier transform of the Poisson kernel.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Set UpperHalfPlane ModularGroup
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower
open GaloisForLFunctions.ArithmeticCorrespondencePositivity

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-! ### List sums under integrals -/

theorem integrable_and_integral_list_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (l : List ι) (f : ι → α → ℂ) (h : ∀ i ∈ l, Integrable (f i) μ) :
    Integrable (fun a => (l.map fun i => f i a).sum) μ ∧
      ∫ a, (l.map fun i => f i a).sum ∂μ = (l.map fun i => ∫ a, f i a ∂μ).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := ih fun j hj => h j (List.mem_cons_of_mem i hj)
    have hi := h i List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hi.add h1, by rw [integral_add hi h1, h2]⟩

/-! ### Hecke words -/

/-- The iterated physical Hecke operator on functions of `(x, y)`. -/
def heckeWord : List ℕ → (ℝ → ℝ → ℂ) → ℝ → ℝ → ℂ
  | [], F => F
  | p :: w, F => heckeOp p (heckeWord w F)

/-- The logarithmic shifts of a word: every choice of signs in `Σ ± log p`. -/
def heckeLogs : List ℕ → List ℝ
  | [] => [0]
  | p :: w => (heckeLogs w).map (· + Real.log p) ++ (heckeLogs w).map (· - Real.log p)

/-- The normalized cutoff family `S(x) = e^{ux} t_{Ye^x}` in real coordinates. -/
def shiftedLeg (u : ℂ) (Y x a b : ℝ) : ℂ :=
  cexp (u * x) * truncatedLeg u (Y * Real.exp x) a b

theorem heckeOp_congr {p : ℕ} {F G : ℝ → ℝ → ℂ} (hp : 0 < p)
    (h : ∀ a b, 0 < b → F a b = G a b) {a b : ℝ} (hb : 0 < b) :
    heckeOp p F a b = heckeOp p G a b := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold heckeOp
  rw [h _ _ (mul_pos hpR hb)]
  congr 2
  exact Finset.sum_congr rfl fun j _ => h _ _ (div_pos hb hpR)

theorem heckeOp_const_mul (p : ℕ) (c : ℂ) (F : ℝ → ℝ → ℂ) (a b : ℝ) :
    heckeOp p (fun a b => c * F a b) a b = c * heckeOp p F a b := by
  unfold heckeOp
  rw [← Finset.mul_sum]
  ring

theorem heckeOp_list_sum (p : ℕ) {ι : Type*} (l : List ι) (f : ι → ℝ → ℝ → ℂ) (a b : ℝ) :
    heckeOp p (fun a b => (l.map fun i => f i a b).sum) a b
      = (l.map fun i => heckeOp p (f i) a b).sum := by
  induction l with
  | nil =>
    simp [heckeOp]
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    unfold heckeOp
    rw [← mul_add]
    congr 1
    rw [add_add_add_comm, ← Finset.sum_add_distrib]

/-- `T_p` acts on the normalized family by the two translations `x ↦ x ± log p`. -/
theorem heckeOp_shiftedLeg {p : ℕ} (hp : p.Prime) {u : ℂ} (hAu : msA u = 0) (Y x a : ℝ) {b : ℝ}
    (hb : 0 < b) :
    heckeOp p (shiftedLeg u Y x) a b
      = shiftedLeg u Y (x + Real.log p) a b + shiftedLeg u Y (x - Real.log p) a b := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set z : ℍ := ⟨(a : ℂ) + b * I, by simpa using hb⟩ with hz
  have hre : z.re = a := by simp [hz, UpperHalfPlane.re]
  have him : z.im = b := by simp [hz, UpperHalfPlane.im]
  have hshift := hecke_cutoff_shifts hp hAu (Y * Real.exp x) z
  rw [heckeTruncated, truncatedLineModel_eq_truncatedLeg, truncatedLineModel_eq_truncatedLeg,
    hre, him] at hshift
  have hpow : (p : ℂ) ^ u = cexp (u * (Real.log p : ℝ)) := by
    rw [Complex.cpow_def_of_ne_zero hpC, show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_log hpR.le, mul_comm]
  have hpow' : (p : ℂ) ^ (-u) = cexp (-(u * (Real.log p : ℝ))) := by
    rw [Complex.cpow_neg, hpow, Complex.exp_neg]
  have e1 : Y * Real.exp x * p = Y * Real.exp (x + Real.log p) := by
    rw [Real.exp_add, Real.exp_log hpR]
    ring
  have e2 : Y * Real.exp x / p = Y * Real.exp (x - Real.log p) := by
    rw [Real.exp_sub, Real.exp_log hpR]
    ring
  have hL : heckeOp p (shiftedLeg u Y x) a b
      = cexp (u * x) * heckeOp p (fun a b => truncatedLeg u (Y * Real.exp x) a b) a b :=
    heckeOp_const_mul p _ _ a b
  rw [hL, hshift, e1, e2, hpow, hpow', shiftedLeg, shiftedLeg, mul_add, ← mul_assoc, ← mul_assoc,
    ← Complex.exp_add, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **A Hecke word on the truncated state is a sum of translations.** -/
theorem heckeWord_truncatedLeg {u : ℂ} (hAu : msA u = 0) (Y : ℝ) {w : List ℕ}
    (hw : ∀ p ∈ w, p.Prime) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    heckeWord w (truncatedLeg u Y) a b = ((heckeLogs w).map fun x => shiftedLeg u Y x a b).sum := by
  induction w generalizing a b with
  | nil =>
    simp [heckeWord, heckeLogs, shiftedLeg]
  | cons p w ih =>
    have hp : p.Prime := hw p List.mem_cons_self
    have hw' : ∀ q ∈ w, q.Prime := fun q hq => hw q (List.mem_cons_of_mem p hq)
    have hstep : heckeOp p (heckeWord w (truncatedLeg u Y)) a b
        = heckeOp p (fun a b => ((heckeLogs w).map fun x => shiftedLeg u Y x a b).sum) a b :=
      heckeOp_congr hp.pos (fun a b hb => ih hw' a hb) hb
    change heckeOp p (heckeWord w (truncatedLeg u Y)) a b = _
    rw [hstep, heckeOp_list_sum]
    have hmap : (heckeLogs w).map (fun x => heckeOp p (shiftedLeg u Y x) a b)
        = (heckeLogs w).map (fun x =>
            shiftedLeg u Y (x + Real.log p) a b + shiftedLeg u Y (x - Real.log p) a b) :=
      List.map_congr_left fun x _ => heckeOp_shiftedLeg hp hAu Y x a hb
    rw [hmap, List.sum_map_add]
    simp only [heckeLogs, List.map_append, List.map_map, List.sum_append, Function.comp_def]

theorem one_le_prod_of_prime {w : List ℕ} (hw : ∀ p ∈ w, p.Prime) : (1 : ℝ) ≤ (w.prod : ℕ) := by
  induction w with
  | nil => simp
  | cons p w ih =>
    have hp : (1 : ℝ) ≤ p := by exact_mod_cast (hw p List.mem_cons_self).one_lt.le
    have h := ih fun q hq => hw q (List.mem_cons_of_mem p hq)
    rw [List.prod_cons]
    push_cast
    nlinarith

/-- Every shift of a word is at least `−log Π w`. -/
theorem neg_log_prod_le_of_mem_heckeLogs {w : List ℕ} (hw : ∀ p ∈ w, p.Prime) {x : ℝ}
    (hx : x ∈ heckeLogs w) : -Real.log (w.prod : ℕ) ≤ x := by
  induction w generalizing x with
  | nil =>
    simp only [heckeLogs, List.mem_singleton] at hx
    simp [hx]
  | cons p w ih =>
    have hp : (1 : ℝ) ≤ p := by exact_mod_cast (hw p List.mem_cons_self).one_lt.le
    have hw' : ∀ q ∈ w, q.Prime := fun q hq => hw q (List.mem_cons_of_mem p hq)
    have hprod := one_le_prod_of_prime hw'
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp
    have hsplit : Real.log ((p :: w).prod : ℕ) = Real.log p + Real.log (w.prod : ℕ) := by
      rw [List.prod_cons]
      push_cast
      exact Real.log_mul (by linarith) (by linarith)
    rw [hsplit]
    simp only [heckeLogs, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨x₀, hx₀, rfl⟩ | ⟨x₀, hx₀, rfl⟩
    · have := ih hw' hx₀
      linarith
    · have := ih hw' hx₀
      linarith

theorem one_le_mul_exp_of_mem_heckeLogs {w : List ℕ} (hw : ∀ p ∈ w, p.Prime) {Y x : ℝ}
    (hY : ((w.prod : ℕ) : ℝ) ≤ Y) (hx : x ∈ heckeLogs w) : 1 ≤ Y * Real.exp x := by
  have hprod := one_le_prod_of_prime hw
  have hlow := neg_log_prod_le_of_mem_heckeLogs hw hx
  have hexp : ((w.prod : ℕ) : ℝ)⁻¹ ≤ Real.exp x := by
    have h := Real.exp_le_exp.mpr hlow
    rwa [Real.exp_neg, Real.exp_log (by linarith)] at h
  have hP : (0 : ℝ) < ((w.prod : ℕ) : ℝ) := by linarith
  calc (1 : ℝ) = ((w.prod : ℕ) : ℝ) * ((w.prod : ℕ) : ℝ)⁻¹ := (mul_inv_cancel₀ hP.ne').symm
    _ ≤ Y * Real.exp x := mul_le_mul hY hexp (inv_nonneg.mpr hP.le) (by linarith)

/-! ### The stationary covariance -/

/-- The covariance `e^{−σ|y| + i t₀ y}` of the normalized resonant family. -/
def poissonCovariance (u : ℂ) (y : ℝ) : ℂ :=
  cexp (((-(-u.re) * |y| : ℝ) : ℂ) + I * ((u.im * y : ℝ) : ℂ))

theorem exp_gram_exponent (u : ℂ) (x x' : ℝ) :
    cexp (u * x + conj u * x' + (min x x' : ℝ) * (-u - conj u)) = poissonCovariance u (x - x') := by
  rw [poissonCovariance]
  congr 1
  have hu : u = (u.re : ℂ) + I * (u.im : ℂ) := by
    rw [mul_comm]
    exact (Complex.re_add_im u).symm
  have huc : conj u = (u.re : ℂ) - I * (u.im : ℂ) := by
    conv_lhs => rw [hu]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rcases le_total x' x with h | h
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h), huc]
    conv_lhs => rw [hu]
    push_cast
    ring
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h), huc]
    conv_lhs => rw [hu]
    push_cast
    ring

private theorem integrable_truncated_mul_conj (u : ℂ) {Y Z : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    IntegrableOn (fun z : ℍ => truncatedLineModel u Y z * conj (truncatedLineModel u Z z)) fd := by
  refine Measure.integrableOn_of_bounded volume_fd_ne_top
    ((measurable_truncatedLineModel u Y).mul
      ((Complex.continuous_conj.measurable).comp
        (measurable_truncatedLineModel u Z))).aestronglyMeasurable
    (M := truncBound' u Y * truncBound' u Z) ?_
  refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Eventually.of_forall fun z hz => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (norm_truncatedLineModel_le_truncBound' u hY hz)
    (norm_truncatedLineModel_le_truncBound' u hZ hz) (norm_nonneg _)
    ((norm_nonneg _).trans (norm_truncatedLineModel_le_truncBound' u hY hz))

theorem ofReal_mul_exp_cpow {Y : ℝ} (hY : 0 < Y) (m : ℝ) (s : ℂ) :
    ((Y * Real.exp m : ℝ) : ℂ) ^ s = (Y : ℂ) ^ s * cexp ((m : ℂ) * s) := by
  have hE : ((Real.exp m : ℝ) : ℂ) ^ s = cexp ((m : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos m).ne'),
      ← Complex.ofReal_log (Real.exp_pos m).le, Real.log_exp]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hY.le (Real.exp_pos m).le, hE]

/-- **Stationarity.**  `⟨S(x), S(x')⟩ = ⟨t_Y, t_Y⟩ · e^{−σ|x−x'| + i t₀ (x−x')}`. -/
theorem integral_shifted_mul_conj {u : ℂ} (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0)
    (hAu : msA u = 0) {Y x x' : ℝ} (hY : 1 ≤ Y) (hx : 1 ≤ Y * Real.exp x)
    (hx' : 1 ≤ Y * Real.exp x') :
    ∫ z in fd, (cexp (u * x) * truncatedLineModel u (Y * Real.exp x) z) *
        conj (cexp (u * x') * truncatedLineModel u (Y * Real.exp x') z)
      = (∫ z in fd, truncatedLineModel u Y z * conj (truncatedLineModel u Y z)) *
        poissonCovariance u (x - x') := by
  have hY0 : 0 < Y := by linarith
  have hgram := resonant_cutoff_gram hu hu hur hur hAu hAu hx hx'
  have hgramY := resonant_cutoff_gram hu hu hur hur hAu hAu hY hY
  have hmin : min (Y * Real.exp x) (Y * Real.exp x') = Y * Real.exp (min x x') := by
    rcases le_total x x' with h | h
    · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hY0.le)]
    · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hY0.le)]
  have hfun : (fun z : ℍ => (cexp (u * x) * truncatedLineModel u (Y * Real.exp x) z) *
      conj (cexp (u * x') * truncatedLineModel u (Y * Real.exp x') z))
      = fun z : ℍ => (cexp (u * x) * conj (cexp (u * x'))) *
        (truncatedLineModel u (Y * Real.exp x) z *
          conj (truncatedLineModel u (Y * Real.exp x') z)) := by
    funext z
    rw [map_mul]
    ring
  rw [hfun, integral_const_mul, hgram, hgramY, hmin, min_self, ofReal_mul_exp_cpow hY0,
    ← exp_gram_exponent, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.exp_add,
    Complex.exp_add]
  ring

/-! ### The Poisson mixture -/

/-- The tempered eigenvalue `Π_{p∈w} 2 cos(t log p)` of a word. -/
def wordSymbol (w : List ℕ) (t : ℝ) : ℝ :=
  (w.map fun p => 2 * Real.cos (t * Real.log p)).prod

theorem wordSymbol_neg (w : List ℕ) (t : ℝ) : wordSymbol w (-t) = wordSymbol w t := by
  unfold wordSymbol
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [neg_mul, Real.cos_neg]

theorem sum_exp_heckeLogs (w : List ℕ) (t : ℝ) :
    ((heckeLogs w).map fun x => cexp (I * (x : ℂ) * (t : ℂ))).sum = (wordSymbol w t : ℂ) := by
  induction w with
  | nil => simp [heckeLogs, wordSymbol]
  | cons p w ih =>
    have hcos : cexp (I * (Real.log p : ℂ) * t) + cexp (-(I * (Real.log p : ℂ) * t))
        = ((2 * Real.cos (t * Real.log p) : ℝ) : ℂ) := by
      push_cast
      rw [Complex.cos, show (t : ℂ) * (Real.log p : ℂ) * I = I * (Real.log p : ℂ) * t by ring,
        show -((t : ℂ) * (Real.log p : ℂ)) * I = -(I * (Real.log p : ℂ) * t) by ring]
      ring
    have hmap1 : (heckeLogs w).map (fun x : ℝ => cexp (I * ((x + Real.log p : ℝ) : ℂ) * t))
        = (heckeLogs w).map (fun x : ℝ =>
            cexp (I * (Real.log p : ℂ) * t) * cexp (I * (x : ℂ) * t)) :=
      List.map_congr_left fun x _ => by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    have hmap2 : (heckeLogs w).map (fun x : ℝ => cexp (I * ((x - Real.log p : ℝ) : ℂ) * t))
        = (heckeLogs w).map (fun x : ℝ =>
            cexp (-(I * (Real.log p : ℂ) * t)) * cexp (I * (x : ℂ) * t)) :=
      List.map_congr_left fun x _ => by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    simp only [heckeLogs, List.map_append, List.map_map, List.sum_append, Function.comp_def]
    rw [hmap1, hmap2, List.sum_map_mul_left, List.sum_map_mul_left, ih, ← add_mul, hcos, wordSymbol,
      List.map_cons, List.prod_cons]
    push_cast
    rfl

/-- The Poisson mixture of the shifts of two words. -/
theorem integral_poisson_mul_wordSymbol {u : ℂ} (hur : u.re < 0) (w w' : List ℕ) :
    ∫ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
        ((wordSymbol w t : ℂ) * (wordSymbol w' t : ℂ))
      = ((heckeLogs w).map fun x =>
          ((heckeLogs w').map fun x' => poissonCovariance u (x - x')).sum).sum := by
  have hσ : 0 < -u.re := neg_pos.mpr hur
  have hint : ∀ y : ℝ, Integrable (fun t : ℝ =>
      (halfPlanePoisson (-u.re) (t - u.im) : ℂ) * cexp (I * (y : ℂ) * (t : ℂ))) :=
    fun y => integrable_halfPlanePoisson_shift_mul_cexp hσ u.im y
  have hval : ∀ y : ℝ, ∫ t : ℝ,
      (halfPlanePoisson (-u.re) (t - u.im) : ℂ) * cexp (I * (y : ℂ) * (t : ℂ))
      = poissonCovariance u y := fun y =>
    integral_halfPlanePoisson_shift_mul_cexp hσ u.im y
  have hfun : (fun t : ℝ => (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
      ((wordSymbol w t : ℂ) * (wordSymbol w' t : ℂ)))
      = fun t : ℝ => ((heckeLogs w).map fun x => ((heckeLogs w').map fun x' =>
          (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
            cexp (I * ((x - x' : ℝ) : ℂ) * (t : ℂ))).sum).sum := by
    funext t
    have h2 : (wordSymbol w' t : ℂ)
        = ((heckeLogs w').map fun x' => cexp (I * (x' : ℂ) * ((-t : ℝ) : ℂ))).sum := by
      rw [sum_exp_heckeLogs, wordSymbol_neg]
    rw [← sum_exp_heckeLogs w t, h2]
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun x' _ => ?_
    rw [mul_assoc]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hinner : ∀ x : ℝ,
      Integrable (fun t : ℝ => ((heckeLogs w').map fun x' =>
          (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
            cexp (I * ((x - x' : ℝ) : ℂ) * (t : ℂ))).sum) ∧
      ∫ t : ℝ, ((heckeLogs w').map fun x' =>
          (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
            cexp (I * ((x - x' : ℝ) : ℂ) * (t : ℂ))).sum
        = ((heckeLogs w').map fun x' => poissonCovariance u (x - x')).sum := by
    intro x
    obtain ⟨h1, h2⟩ := integrable_and_integral_list_sum (μ := volume) (heckeLogs w')
      (fun x' t => (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
        cexp (I * ((x - x' : ℝ) : ℂ) * (t : ℂ))) (fun x' _ => hint (x - x'))
    refine ⟨h1, h2.trans ?_⟩
    congr 1
    exact List.map_congr_left fun x' _ => hval (x - x')
  obtain ⟨-, houter⟩ := integrable_and_integral_list_sum (μ := volume) (heckeLogs w)
    (fun x t => ((heckeLogs w').map fun x' =>
      (halfPlanePoisson (-u.re) (t - u.im) : ℂ) * cexp (I * ((x - x' : ℝ) : ℂ) * (t : ℂ))).sum)
    (fun x _ => (hinner x).1)
  rw [hfun, houter]
  congr 1
  exact List.map_congr_left fun x _ => (hinner x).2

/-- **Physical mixed Hecke moments.**  On a truncated resonant state, the Hecke algebra has the Poisson
kernel at `u` as joint spectral measure, for arbitrary words in the primes. -/
theorem integral_heckeWord_mul_conj_heckeWord {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {w w' : List ℕ} (hw : ∀ p ∈ w, p.Prime)
    (hw' : ∀ p ∈ w', p.Prime) {Y : ℝ} (hY : ((w.prod : ℕ) : ℝ) ≤ Y) (hY' : ((w'.prod : ℕ) : ℝ) ≤ Y) :
    ∫ z in fd, heckeWord w (truncatedLeg u Y) z.re z.im *
        conj (heckeWord w' (truncatedLeg u Y) z.re z.im)
      = (∫ z in fd, truncatedLineModel u Y z * conj (truncatedLineModel u Y z)) *
        ∫ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          ((wordSymbol w t : ℂ) * (wordSymbol w' t : ℂ)) := by
  have hY1 : 1 ≤ Y := (one_le_prod_of_prime hw).trans hY
  set S : ℝ → ℍ → ℂ := fun x z => cexp (u * x) * truncatedLineModel u (Y * Real.exp x) z with hS
  have hpoint : ∀ (v : List ℕ), (∀ p ∈ v, p.Prime) → ∀ z : ℍ,
      heckeWord v (truncatedLeg u Y) z.re z.im = ((heckeLogs v).map fun x => S x z).sum := by
    intro v hv z
    rw [heckeWord_truncatedLeg hAu Y hv z.re z.im_pos]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [shiftedLeg, hS, truncatedLineModel_eq_truncatedLeg]
  have hfun : (fun z : ℍ => heckeWord w (truncatedLeg u Y) z.re z.im *
      conj (heckeWord w' (truncatedLeg u Y) z.re z.im))
      = fun z : ℍ => ((heckeLogs w).map fun x =>
          ((heckeLogs w').map fun x' => S x z * conj (S x' z)).sum).sum := by
    funext z
    rw [hpoint w hw z, hpoint w' hw' z, map_list_sum, List.map_map]
    rw [← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [← List.sum_map_mul_left]
    simp only [Function.comp_def]
  have hintS : ∀ x ∈ heckeLogs w, ∀ x' ∈ heckeLogs w',
      Integrable (fun z : ℍ => S x z * conj (S x' z)) (volume.restrict fd) := by
    intro x hx x' hx'
    have h := integrable_truncated_mul_conj u (one_le_mul_exp_of_mem_heckeLogs hw hY hx)
      (one_le_mul_exp_of_mem_heckeLogs hw' hY' hx')
    have hconst := (h.const_mul (cexp (u * x) * conj (cexp (u * x'))))
    refine hconst.congr (Eventually.of_forall fun z => ?_)
    simp only [hS, map_mul]
    ring
  have hinner : ∀ x ∈ heckeLogs w,
      Integrable (fun z : ℍ => ((heckeLogs w').map fun x' => S x z * conj (S x' z)).sum)
        (volume.restrict fd) ∧
      ∫ z in fd, ((heckeLogs w').map fun x' => S x z * conj (S x' z)).sum
        = (∫ z in fd, truncatedLineModel u Y z * conj (truncatedLineModel u Y z)) *
          ((heckeLogs w').map fun x' => poissonCovariance u (x - x')).sum := by
    intro x hx
    obtain ⟨h1, h2⟩ := integrable_and_integral_list_sum (μ := volume.restrict fd) (heckeLogs w')
      (fun x' z => S x z * conj (S x' z)) (fun x' hx' => hintS x hx x' hx')
    refine ⟨h1, h2.trans ?_⟩
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun x' hx' => ?_
    exact integral_shifted_mul_conj hu hur hAu hY1 (one_le_mul_exp_of_mem_heckeLogs hw hY hx)
      (one_le_mul_exp_of_mem_heckeLogs hw' hY' hx')
  obtain ⟨-, houter⟩ := integrable_and_integral_list_sum (μ := volume.restrict fd) (heckeLogs w)
    (fun x z => ((heckeLogs w').map fun x' => S x z * conj (S x' z)).sum)
    (fun x hx => (hinner x hx).1)
  rw [hfun, houter, integral_poisson_mul_wordSymbol hur, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun x hx => (hinner x hx).2

/-! ### Squarefree words read the formal moment -/

theorem whittakerCoeff_I_mul_prime {p : ℕ} (hp : p.Prime) (t : ℝ) :
    whittakerCoeff (I * (t : ℂ)) p = ((2 * Real.cos (t * Real.log p) : ℝ) : ℂ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [whittakerCoeff_prime _ hp, Complex.cpow_neg, Complex.cpow_def_of_ne_zero hpC,
    show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_log hpR.le,
    ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, show (t : ℂ) * (Real.log p : ℂ) * I = (Real.log p : ℂ) * (I * t) by ring,
    show -((t : ℂ) * (Real.log p : ℂ)) * I = -((Real.log p : ℂ) * (I * t)) by ring]
  ring

/-- On a product of pairwise coprime primes the symbol is the Whittaker eigenvalue. -/
theorem whittakerCoeff_I_mul_prod {w : List ℕ} (hw : ∀ p ∈ w, p.Prime)
    (hco : w.Pairwise Nat.Coprime) (t : ℝ) :
    whittakerCoeff (I * (t : ℂ)) (w.prod : ℕ) = (wordSymbol w t : ℂ) := by
  induction w with
  | nil => simp [wordSymbol]
  | cons p w ih =>
    have hp := hw p List.mem_cons_self
    have hw' : ∀ q ∈ w, q.Prime := fun q hq => hw q (List.mem_cons_of_mem p hq)
    have hco' := List.pairwise_cons.mp hco
    have hcop : p.Coprime w.prod := Nat.Coprime.prod_right_of_list? hco'.1
    sorry

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
