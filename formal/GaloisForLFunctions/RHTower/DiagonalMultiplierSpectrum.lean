import GaloisForLFunctions.RHTower.DeningerTwoPrimeKummerDenseNonclosedRange
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# The spectrum of a diagonal multiplier on `ℓ²`

A bounded diagonal multiplier on `ℓ²` has spectrum the closure of its symbol values, point
spectrum exactly the symbol values, and a singular Weyl sequence at every accumulation value of
the symbol along an injective family of modes.

* `spectrum_deningerMultiplier` : `σ(B) = closure (range g)`;
* `hasEigenvalue_deningerMultiplier` and `mem_range_of_eigenvalue` : the point spectrum is
  `range g`;
* `tendsto_weylSequence` : coordinate modes along an injective family are an orthonormal singular
  Weyl sequence for any limit of their symbol values.
-/

open Filter
open scoped Topology InnerProductSpace ENNReal

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

variable {ι : Type*} [DecidableEq ι]

theorem norm_lp_single_one (i : ι) : ‖(lp.single 2 i (1 : ℂ) : lp (fun _ : ι => ℂ) 2)‖ = 1 := by
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

theorem lp_single_ne_zero (i : ι) :
    (lp.single 2 i (1 : ℂ) : lp (fun _ : ι => ℂ) 2) ≠ 0 := by
  intro h
  have := norm_lp_single_one (ι := ι) i
  rw [h, norm_zero] at this
  norm_num at this

/-- A diagonal multiplier acts on a coordinate mode by its symbol value. -/
theorem multiplier_apply_single {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) (i : ι) (c : ℂ) :
    deningerMultiplier hg (lp.single 2 i c) = lp.single 2 i (g i * c) :=
  deningerMultiplier_single hg i c

/-- Every symbol value is an eigenvalue, realized by its coordinate mode. -/
theorem hasEigenvalue_deningerMultiplier {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) (i : ι) :
    deningerMultiplier hg (lp.single 2 i (1 : ℂ)) = g i • lp.single 2 i (1 : ℂ) := by
  rw [multiplier_apply_single, mul_one]
  apply lp.ext
  funext j
  by_cases hj : j = i
  · subst hj
    simp [lp.single_apply]
  · simp [lp.single_apply, hj]

omit [DecidableEq ι] in
/-- Conversely, every eigenvalue is a symbol value. -/
theorem mem_range_of_eigenvalue {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) {lam : ℂ}
    {x : lp (fun _ : ι => ℂ) 2} (hx : x ≠ 0)
    (heig : deningerMultiplier hg x = lam • x) : lam ∈ Set.range g := by
  by_contra hcon
  apply hx
  apply lp.ext
  funext i
  have hcoord : g i * (x : ι → ℂ) i = lam * (x : ι → ℂ) i := by
    have h := congrArg (fun z : lp (fun _ : ι => ℂ) 2 => (z : ι → ℂ) i) heig
    simpa [deningerMultiplier_apply] using h
  have hne : g i - lam ≠ 0 := by
    intro h0
    exact hcon ⟨i, by linear_combination h0⟩
  have : (g i - lam) * (x : ι → ℂ) i = 0 := by linear_combination hcoord
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hne
  · simpa using h

section Spectrum

variable [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Off the closure of the symbol values the shifted multiplier is invertible. -/
theorem isUnit_sub_deningerMultiplier {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) {lam : ℂ}
    (hlam : lam ∉ closure (Set.range g)) :
    IsUnit (algebraMap ℂ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) lam
      - deningerMultiplier hg) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_closure (s := Set.range g)).isOpen_compl
    lam hlam
  have hgap : ∀ i, ε ≤ ‖lam - g i‖ := by
    intro i
    by_contra hcon
    push Not at hcon
    have hmem : g i ∈ Metric.ball lam ε := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
      exact hcon
    exact (hball hmem) (subset_closure ⟨i, rfl⟩)
  have hne : ∀ i, lam - g i ≠ 0 := by
    intro i h0
    have hi := hgap i
    rw [h0, norm_zero] at hi
    linarith
  set h : ι → ℂ := fun i => (ε : ℂ) * (lam - g i)⁻¹ with hhdef
  have hhb : ∀ i, ‖h i‖ ≤ 1 := by
    intro i
    have hpos : 0 < ‖lam - g i‖ := lt_of_lt_of_le hε (hgap i)
    show ‖(ε : ℂ) * (lam - g i)⁻¹‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hε.le,
      inv_eq_one_div, mul_one_div, div_le_one hpos]
    exact hgap i
  set M := deningerMultiplier hhb with hM
  set A := algebraMap ℂ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) lam
    - deningerMultiplier hg with hA
  have hAapply : ∀ (x : lp (fun _ : ι => ℂ) 2) (i : ι),
      (A x : ι → ℂ) i = (lam - g i) * (x : ι → ℂ) i := by
    intro x i
    have h1 : ((A x : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
        = lam * (x : ι → ℂ) i - g i * (x : ι → ℂ) i := by
      rw [hA]
      simp [deningerMultiplier_apply, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    ring
  have hsmul : ∀ (x : lp (fun _ : ι => ℂ) 2) (i : ι),
      (((ε : ℂ) • x : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i = (ε : ℂ) * (x : ι → ℂ) i := by
    intro x i
    rw [lp.coeFn_smul]
    rfl
  have hMA : ∀ x : lp (fun _ : ι => ℂ) 2, M (A x) = (ε : ℂ) • x := by
    intro x
    apply lp.ext
    funext i
    rw [deningerMultiplier_apply, hAapply, hsmul]
    show (ε : ℂ) * (lam - g i)⁻¹ * ((lam - g i) * (x : ι → ℂ) i)
      = (ε : ℂ) * (x : ι → ℂ) i
    have h1 : (lam - g i)⁻¹ * (lam - g i) = 1 := inv_mul_cancel₀ (hne i)
    calc (ε : ℂ) * (lam - g i)⁻¹ * ((lam - g i) * (x : ι → ℂ) i)
        = (ε : ℂ) * ((lam - g i)⁻¹ * (lam - g i)) * (x : ι → ℂ) i := by ring
      _ = (ε : ℂ) * (x : ι → ℂ) i := by rw [h1, mul_one]
  have hAM : ∀ x : lp (fun _ : ι => ℂ) 2, A (M x) = (ε : ℂ) • x := by
    intro x
    apply lp.ext
    funext i
    rw [hAapply, deningerMultiplier_apply, hsmul]
    show (lam - g i) * ((ε : ℂ) * (lam - g i)⁻¹ * (x : ι → ℂ) i)
      = (ε : ℂ) * (x : ι → ℂ) i
    have h1 : (lam - g i) * (lam - g i)⁻¹ = 1 := mul_inv_cancel₀ (hne i)
    calc (lam - g i) * ((ε : ℂ) * (lam - g i)⁻¹ * (x : ι → ℂ) i)
        = (ε : ℂ) * ((lam - g i) * (lam - g i)⁻¹) * (x : ι → ℂ) i := by ring
      _ = (ε : ℂ) * (x : ι → ℂ) i := by rw [h1, mul_one]
  have hεne : (ε : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hε.ne'
  refine ⟨⟨A, ((ε : ℂ)⁻¹ • M), ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    simp only [mul_apply_eq_comp, one_apply_eq_self, smul_apply]
    rw [map_smul, hAM, smul_smul, inv_mul_cancel₀ hεne, one_smul]
  · refine ContinuousLinearMap.ext fun x => ?_
    simp only [mul_apply_eq_comp, one_apply_eq_self, smul_apply]
    rw [hMA, smul_smul, inv_mul_cancel₀ hεne, one_smul]

/-- On the closure of the symbol values the shifted multiplier is not invertible. -/
theorem not_isUnit_sub_deningerMultiplier {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) {lam : ℂ}
    (hlam : lam ∈ closure (Set.range g)) :
    ¬ IsUnit (algebraMap ℂ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) lam
      - deningerMultiplier hg) := by
  rintro ⟨u, hu⟩
  set A := algebraMap ℂ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) lam
    - deningerMultiplier hg with hA
  have hAapply : ∀ (x : lp (fun _ : ι => ℂ) 2) (i : ι),
      (A x : ι → ℂ) i = (lam - g i) * (x : ι → ℂ) i := by
    intro x i
    have h1 : ((A x : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i
        = lam * (x : ι → ℂ) i - g i * (x : ι → ℂ) i := by
      rw [hA]
      simp [deningerMultiplier_apply, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    ring
  have hinv : ∀ x : lp (fun _ : ι => ℂ) 2, (u.inv : _ →L[ℂ] _) (A x) = x := by
    intro x
    have := congrArg (fun T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 => T x) u.inv_val
    simpa [hu] using this
  have hnormpos : 0 < ‖(u.inv : _ →L[ℂ] _)‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (u.inv : _ →L[ℂ] _)) with h | h
    · exfalso
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hzero : (u.inv : _ →L[ℂ] _) = 0 := by
        rw [← norm_eq_zero]
        exact h.symm
      have := hinv (lp.single 2 i (1 : ℂ))
      rw [hzero] at this
      exact lp_single_ne_zero i this.symm
    · exact h
  have hbound : ∀ i : ι, 1 ≤ ‖(u.inv : _ →L[ℂ] _)‖ * ‖lam - g i‖ := by
    intro i
    have hx := hinv (lp.single 2 i (1 : ℂ))
    have hle := (u.inv : _ →L[ℂ] _).le_opNorm (A (lp.single 2 i (1 : ℂ)))
    rw [hx, norm_lp_single_one] at hle
    have hAnorm : ‖A (lp.single 2 i (1 : ℂ))‖ = ‖lam - g i‖ := by
      have hEq : A (lp.single 2 i (1 : ℂ)) = lp.single 2 i (lam - g i) := by
        apply lp.ext
        funext j
        rw [hAapply]
        by_cases hj : j = i
        · subst hj
          simp [lp.single_apply]
        · simp [lp.single_apply, hj]
      rw [hEq, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    rwa [hAnorm] at hle
  obtain ⟨i, hi⟩ : ∃ i : ι, ‖lam - g i‖ < 1 / ‖(u.inv : _ →L[ℂ] _)‖ := by
    have hpos : 0 < 1 / ‖(u.inv : _ →L[ℂ] _)‖ := by positivity
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hlam _ hpos
    obtain ⟨i, rfl⟩ := hy
    refine ⟨i, ?_⟩
    rwa [dist_eq_norm] at hdist
  have hb := hbound i
  have hlt : ‖(u.inv : _ →L[ℂ] _)‖ * ‖lam - g i‖ < 1 := by
    calc ‖(u.inv : _ →L[ℂ] _)‖ * ‖lam - g i‖
        < ‖(u.inv : _ →L[ℂ] _)‖ * (1 / ‖(u.inv : _ →L[ℂ] _)‖) :=
          mul_lt_mul_of_pos_left hi hnormpos
      _ = 1 := by field_simp
  linarith

/-- **The spectrum of a diagonal multiplier.** -/
theorem spectrum_deningerMultiplier {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) :
    spectrum ℂ (deningerMultiplier hg) = closure (Set.range g) := by
  ext lam
  rw [spectrum.mem_iff]
  constructor
  · intro hmem
    by_contra hcon
    exact hmem (isUnit_sub_deningerMultiplier hg hcon)
  · intro hmem
    exact not_isUnit_sub_deningerMultiplier hg hmem

end Spectrum

/-! ## Singular Weyl sequences -/

/-- Coordinate modes along an injective family form an orthonormal sequence whose symbol defect
tends to zero: a singular Weyl sequence. -/
theorem tendsto_weylSequence {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) {lam : ℂ}
    (q : ℕ → ι) (hlim : Tendsto (fun n => g (q n)) atTop (𝓝 lam)) :
    Tendsto (fun n => ‖deningerMultiplier hg (lp.single 2 (q n) (1 : ℂ))
      - lam • lp.single 2 (q n) (1 : ℂ)‖) atTop (𝓝 0) := by
  have hval : ∀ n, deningerMultiplier hg (lp.single 2 (q n) (1 : ℂ))
      - lam • lp.single 2 (q n) (1 : ℂ) = lp.single 2 (q n) (g (q n) - lam) := by
    intro n
    apply lp.ext
    funext j
    rw [lp.coeFn_sub, Pi.sub_apply, deningerMultiplier_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    by_cases hj : j = q n
    · subst hj
      simp [lp.single_apply]
    · simp [lp.single_apply, hj]
  have hnorm : ∀ n, ‖deningerMultiplier hg (lp.single 2 (q n) (1 : ℂ))
      - lam • lp.single 2 (q n) (1 : ℂ)‖ = ‖g (q n) - lam‖ := by
    intro n
    rw [hval n, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simp only [hnorm]
  have := (hlim.sub (tendsto_const_nhds (x := lam) (f := atTop))).norm
  simpa using this

/-- Coordinate modes along an injective family converge weakly to zero. -/
theorem tendsto_inner_lp_single_zero {q : ℕ → ι} (hq : Function.Injective q)
    (z : lp (fun _ : ι => ℂ) 2) :
    Tendsto (fun n => ⟪z, (lp.single 2 (q n) (1 : ℂ) : lp (fun _ : ι => ℂ) 2)⟫_ℂ)
      atTop (𝓝 0) := by
  have hsum : Summable fun i : ι => ‖(z : ι → ℂ) i‖ ^ (2 : ℝ) :=
    lp.memℓp z |>.summable (by norm_num)
  have hsum' : Summable fun n : ℕ => ‖(z : ι → ℂ) (q n)‖ ^ (2 : ℝ) :=
    hsum.comp_injective hq
  have hzero : Tendsto (fun n => ‖(z : ι → ℂ) (q n)‖ ^ (2 : ℝ)) atTop (𝓝 0) :=
    hsum'.tendsto_atTop_zero
  have hnorm : Tendsto (fun n => ‖(z : ι → ℂ) (q n)‖) atTop (𝓝 0) := by
    have hcont : Tendsto (fun t : ℝ => t ^ ((2 : ℝ)⁻¹)) (𝓝 0) (𝓝 0) := by
      have := Real.continuousAt_rpow_const 0 ((2 : ℝ)⁻¹) (Or.inr (by norm_num))
      simpa using this.tendsto
    have hcomp := hcont.comp hzero
    refine hcomp.congr fun n => ?_
    rw [Function.comp_apply, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hval : ∀ n, ⟪z, (lp.single 2 (q n) (1 : ℂ) : lp (fun _ : ι => ℂ) 2)⟫_ℂ
      = (starRingEnd ℂ) ((z : ι → ℂ) (q n)) := by
    intro n
    rw [lp.inner_single_right]
    simp [RCLike.inner_apply]
  simp only [hval]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using hnorm

end GaloisForLFunctions.RHTower
