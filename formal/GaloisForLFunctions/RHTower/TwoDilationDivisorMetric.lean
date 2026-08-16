import GaloisForLFunctions.RHTower.XiRealDivisorSampling

/-!
# Two prime dilations and the divisor-supported metric

Two multiplicatively independent integer scales act on the logarithmic line by two translations
whose ratio is irrational.  The additive group they generate is therefore dense, and any continuous
function invariant under both translations is constant.  This is the mechanism that upgrades a
discrete two-dilation symmetry of a metric on the line to full translation invariance without
assuming any infinitesimal symmetry.

The second half records the null constraint: if the spectral measure of such a metric annihilates
the completed zeta trace, then it is carried by the real divisor of that trace.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-! ## Multiplicative independence gives an irrational logarithmic ratio -/

/-- Two multiplicatively independent integers `≥ 2` have irrational logarithmic ratio. -/
theorem irrational_log_div_log {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n) :
    Irrational (Real.log r / Real.log s) := by
  rintro ⟨q, hq⟩
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hr
  have hs1 : (1 : ℝ) < (s : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hs
  have hlr : 0 < Real.log r := Real.log_pos hr1
  have hls : 0 < Real.log s := Real.log_pos hs1
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    rw [hq]
    exact div_pos hlr hls
  have hqQ : 0 < q := by exact_mod_cast hqpos
  have hnum : 0 < q.num := Rat.num_pos.mpr hqQ
  have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  have hmul : (q : ℝ) * Real.log s = Real.log r := by
    rw [hq]
    field_simp
  have hfrac : ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (Rat.num_div_den q)
  rw [← hfrac, div_mul_eq_mul_div, div_eq_iff (ne_of_gt hden)] at hmul
  set a : ℕ := q.num.toNat with ha
  have hanumZ : ((a : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt hnum)
  have hanum : ((a : ℕ) : ℝ) = (q.num : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hanumZ
  have hapos : 0 < a := by
    rw [ha]
    omega
  have hlog : Real.log ((r : ℝ) ^ q.den) = Real.log ((s : ℝ) ^ a) := by
    rw [Real.log_pow, Real.log_pow, hanum]
    linarith [hmul]
  have hpow : (r : ℝ) ^ q.den = (s : ℝ) ^ a := by
    have hrp : (0 : ℝ) < (r : ℝ) ^ q.den := by positivity
    have hsp : (0 : ℝ) < (s : ℝ) ^ a := by positivity
    rw [← Real.exp_log hrp, ← Real.exp_log hsp, hlog]
  have hnat : r ^ q.den = s ^ a := by exact_mod_cast hpow
  exact hind q.den a q.pos hapos hnat

/-! ## Density of a two-generator translation group -/

/-- Two reals with irrational ratio generate a dense additive subgroup of the line. -/
theorem dense_closure_pair_of_irrational {x y : ℝ} (hy : y ≠ 0) (hirr : Irrational (x / y)) :
    Dense ((AddSubgroup.closure ({x, y} : Set ℝ) : AddSubgroup ℝ) : Set ℝ) := by
  rcases (AddSubgroup.closure ({x, y} : Set ℝ)).dense_or_cyclic with hd | ⟨c, hc⟩
  · exact hd
  · exfalso
    have hxmem : x ∈ AddSubgroup.closure ({x, y} : Set ℝ) :=
      AddSubgroup.subset_closure (by simp)
    have hymem : y ∈ AddSubgroup.closure ({x, y} : Set ℝ) :=
      AddSubgroup.subset_closure (by simp)
    rw [hc] at hxmem hymem
    obtain ⟨m, hm⟩ := AddSubgroup.mem_closure_singleton.mp hxmem
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hymem
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, smul_zero] at hn
      exact hy hn.symm
    have hn0 : n ≠ 0 := by
      intro h
      rw [h, zero_smul] at hn
      exact hy hn.symm
    refine hirr ⟨(m : ℚ) / (n : ℚ), ?_⟩
    rw [← hm, ← hn, zsmul_eq_mul, zsmul_eq_mul]
    rw [mul_div_mul_right _ _ hc0]
    push_cast
    rfl

/-! ## Invariance under a dense group of translations -/

/-- The additive group of periods of a function on the line. -/
def periodAddSubgroup (f : ℝ → ℂ) : AddSubgroup ℝ where
  carrier := {g : ℝ | ∀ x, f (x + g) = f x}
  zero_mem' := by
    intro x
    rw [add_zero]
  add_mem' := by
    intro a b ha hb x
    rw [← add_assoc, hb (x + a)]
    exact ha x
  neg_mem' := by
    intro a ha x
    have h := ha (x + -a)
    rw [add_assoc, neg_add_cancel, add_zero] at h
    exact h.symm

@[simp]
theorem mem_periodAddSubgroup {f : ℝ → ℂ} {g : ℝ} :
    g ∈ periodAddSubgroup f ↔ ∀ x, f (x + g) = f x := Iff.rfl

/-- **A continuous function with a dense group of periods is constant.** -/
theorem eq_of_continuous_of_dense_periods {f : ℝ → ℂ} (hf : Continuous f)
    (hdense : Dense ((periodAddSubgroup f : AddSubgroup ℝ) : Set ℝ)) (x y : ℝ) :
    f x = f y := by
  have hclosed : IsClosed {t : ℝ | f (x + t) = f x} :=
    isClosed_eq (hf.comp (continuous_const.add continuous_id)) continuous_const
  have hsub : ((periodAddSubgroup f : AddSubgroup ℝ) : Set ℝ) ⊆ {t : ℝ | f (x + t) = f x} :=
    fun g hg => hg x
  have huniv : (Set.univ : Set ℝ) ⊆ {t : ℝ | f (x + t) = f x} := by
    have h := hclosed.closure_subset_iff.mpr hsub
    rwa [hdense.closure_eq] at h
  have hmem : (y - x) ∈ {t : ℝ | f (x + t) = f x} := huniv (Set.mem_univ _)
  have : f (x + (y - x)) = f x := hmem
  rw [add_sub_cancel] at this
  exact this.symm

/-- **Two multiplicatively independent dilations force full translation invariance.**  A continuous
function on the logarithmic line invariant under the two translations by `log r` and `log s` is
constant. -/
theorem eq_of_two_dilation_invariance {f : ℝ → ℂ} (hf : Continuous f) {r s : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hind : ∀ m n : ℕ, 0 < m → 0 < n → r ^ m ≠ s ^ n)
    (hinvr : ∀ x, f (x + Real.log r) = f x) (hinvs : ∀ x, f (x + Real.log s) = f x)
    (x y : ℝ) : f x = f y := by
  have hs1 : (1 : ℝ) < (s : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hs
  have hls : Real.log s ≠ 0 := ne_of_gt (Real.log_pos hs1)
  have hdense := dense_closure_pair_of_irrational hls (irrational_log_div_log hr hs hind)
  have hle : AddSubgroup.closure ({Real.log r, Real.log s} : Set ℝ) ≤ periodAddSubgroup f := by
    rw [AddSubgroup.closure_le]
    rintro g hg
    rcases hg with hg | hg
    · rw [hg]; exact hinvr
    · rw [Set.mem_singleton_iff.mp hg]; exact hinvs
  exact eq_of_continuous_of_dense_periods hf (hdense.mono hle) x y

/-! ## The null constraint carries the metric onto the divisor -/

/-- A measure annihilating the square of a function is carried by the zero set of that
function. -/
theorem measure_setOf_ne_zero_eq_zero {μ : Measure ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (h : ∫⁻ t, (‖g t‖₊ : ENNReal) ^ 2 ∂μ = 0) : μ {t : ℝ | g t ≠ 0} = 0 := by
  have hmeas : Measurable fun t : ℝ => (‖g t‖₊ : ENNReal) ^ 2 :=
    (hg.nnnorm.measurable.coe_nnreal_ennreal).pow_const 2
  have hae := (lintegral_eq_zero_iff hmeas).mp h
  have hsub : {t : ℝ | g t ≠ 0} ⊆ {t : ℝ | (‖g t‖₊ : ENNReal) ^ 2 ≠ 0} := by
    intro t ht
    have hne : (‖g t‖₊ : ENNReal) ≠ 0 := by simpa using ht
    exact pow_ne_zero 2 hne
  refine measure_mono_null hsub ?_
  rw [← MeasureTheory.ae_iff]
  filter_upwards [hae] with t ht
  simpa using ht

/-- **The two-dilation metric is carried by the real Xi divisor.**  A measure annihilating the
completed zeta trace on the line is concentrated on its real divisor. -/
theorem measure_compl_xiRealDivisor_eq_zero {μ : Measure ℝ}
    (h : ∫⁻ t, (‖XiC (t : ℂ)‖₊ : ENNReal) ^ 2 ∂μ = 0) : μ (xiRealDivisorᶜ) = 0 := by
  have hcont : Continuous fun t : ℝ => XiC (t : ℂ) :=
    XiC_differentiable.continuous.comp Complex.continuous_ofReal
  have hzero := measure_setOf_ne_zero_eq_zero hcont h
  have hset : (xiRealDivisorᶜ : Set ℝ) = {t : ℝ | XiC (t : ℂ) ≠ 0} := rfl
  rw [hset]
  exact hzero

end

end RHTower
