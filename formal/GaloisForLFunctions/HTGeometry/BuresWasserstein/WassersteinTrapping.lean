import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinResolventStep

/-!
# Uniform trapping of the resolvent in a Loewner interval

The explicit Euler map `E_h(X) = X - hΦ(X)` pushes a Loewner interval `[a·1, b·1]` strictly
inside itself with a margin linear in `h`, provided `a` lies below and `b` above the bounds of
the data.  The scalar statements behind this are

`x + h(√P x^{-1/2} - 1) ≥ a + h(√P/√a - 1)`   for `x ≥ a`,
`x + h(√Q x^{-1/2} - 1) ≤ b + h(√Q/√b - 1)`   for `a ≤ x ≤ b`,

which after the substitution `x = u²`, `a = v²`, `b = w²` factor as
`(u-v)(uv(u+v) - h√P)/(uv)` and `(w-u)(uw(w+u) - h√Q)/(uw)`, both nonnegative as soon as
`h√Q ≤ 2a√a`.  Since the resolvent differs from the Euler map by `O(h²)`, the margin absorbs
that error for small `h`.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-! ### The scalar inward estimates -/

/-- The Euler map moves points of `[a, ∞)` up by at least the margin at the left endpoint. -/
lemma euler_lower_scalar {a P Q h x : ℝ} (ha : 0 < a) (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (hhE : h * Real.sqrt Q ≤ 2 * a * Real.sqrt a) (hx : a ≤ x) :
    a + h * (Real.sqrt P / Real.sqrt a - 1)
      ≤ x + h * (Real.sqrt P * (Real.sqrt x)⁻¹ - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hPQs : Real.sqrt P ≤ Real.sqrt Q := Real.sqrt_le_sqrt hPQ
  have hPa : (0 : ℝ) < Real.sqrt P := Real.sqrt_pos.mpr hP
  obtain ⟨u, hu, hux⟩ : ∃ u : ℝ, 0 < u ∧ x = u * u :=
    ⟨Real.sqrt x, Real.sqrt_pos.mpr hx0, (Real.mul_self_sqrt hx0.le).symm⟩
  obtain ⟨v, hv, hva⟩ : ∃ v : ℝ, 0 < v ∧ a = v * v :=
    ⟨Real.sqrt a, Real.sqrt_pos.mpr ha, (Real.mul_self_sqrt ha.le).symm⟩
  subst hux
  subst hva
  rw [Real.sqrt_mul_self hu.le, Real.sqrt_mul_self hv.le] at *
  have huv : v ≤ u := by nlinarith [hx, hu, hv]
  rw [← sub_nonneg]
  have key : u * u + h * (Real.sqrt P * u⁻¹ - 1) - (v * v + h * (Real.sqrt P / v - 1))
      = (u - v) * (u * v * (u + v) - h * Real.sqrt P) / (u * v) := by
    field_simp
    ring
  rw [key]
  refine div_nonneg (mul_nonneg (by linarith) ?_) (by positivity)
  have hcube : 2 * (v * v) * v ≤ u * v * (u + v) := by nlinarith [huv, hu, hv]
  nlinarith [hcube, hhE, hPQs, hh.le]

/-- The Euler map moves points of `[a, b]` down by at least the margin at the right endpoint. -/
lemma euler_upper_scalar {a b Q h x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hQ : 0 < Q) (_hh : 0 < h)
    (hhE : h * Real.sqrt Q ≤ 2 * a * Real.sqrt a) (hx : a ≤ x) (hxb : x ≤ b) :
    x + h * (Real.sqrt Q * (Real.sqrt x)⁻¹ - 1)
      ≤ b + h * (Real.sqrt Q / Real.sqrt b - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hQa : (0 : ℝ) < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  obtain ⟨u, hu, hux⟩ : ∃ u : ℝ, 0 < u ∧ x = u * u :=
    ⟨Real.sqrt x, Real.sqrt_pos.mpr hx0, (Real.mul_self_sqrt hx0.le).symm⟩
  obtain ⟨v, hv, hva⟩ : ∃ v : ℝ, 0 < v ∧ a = v * v :=
    ⟨Real.sqrt a, Real.sqrt_pos.mpr ha, (Real.mul_self_sqrt ha.le).symm⟩
  obtain ⟨wb, hwb, hwbb⟩ : ∃ wb : ℝ, 0 < wb ∧ b = wb * wb :=
    ⟨Real.sqrt b, Real.sqrt_pos.mpr hb0, (Real.mul_self_sqrt hb0.le).symm⟩
  subst hux
  subst hva
  subst hwbb
  rw [Real.sqrt_mul_self hu.le, Real.sqrt_mul_self hv.le, Real.sqrt_mul_self hwb.le] at *
  have huv : v ≤ u := by nlinarith [hx, hu, hv]
  have huw : u ≤ wb := by nlinarith [hxb, hu, hwb]
  have hvw : v ≤ wb := le_trans huv huw
  rw [← sub_nonneg]
  have key : wb * wb + h * (Real.sqrt Q / wb - 1) - (u * u + h * (Real.sqrt Q * u⁻¹ - 1))
      = (wb - u) * (u * wb * (wb + u) - h * Real.sqrt Q) / (u * wb) := by
    field_simp
    ring
  rw [key]
  refine div_nonneg (mul_nonneg (by linarith) ?_) (by positivity)
  have hcube : 2 * (v * v) * v ≤ u * wb * (wb + u) := by nlinarith [huv, huw, hvw, hu, hv, hwb]
  linarith [hcube, hhE]

/-! ### The operator inward estimates -/

/-- The continuous functional calculus form of the lower inward estimate. -/
theorem smul_one_le_euler_lower {X : A} (hX : IsStrictlyPositive X) {a P Q h : ℝ}
    (ha : 0 < a) (hP : 0 < P) (hPQ : P ≤ Q) (hh : 0 < h)
    (hhE : h * Real.sqrt Q ≤ 2 * a * Real.sqrt a) (hXa : a • (1 : A) ≤ X) :
    (a + h * (Real.sqrt P / Real.sqrt a - 1)) • (1 : A)
      ≤ X + (h * Real.sqrt P) • (X ^ (-(1/2) : ℝ)) - h • (1 : A) := by
  have hXsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ X, a ≤ x := by
    rw [← algebraMap_le_iff_le_spectrum (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXa
  have hne : ∀ x ∈ spectrum ℝ X, Real.sqrt x ≠ 0 := fun x hx =>
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le ha (hspec x hx)))
  have hcinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ X) :=
    ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) hne
  have hcmul : ContinuousOn (fun x : ℝ => (h * Real.sqrt P) * (Real.sqrt x)⁻¹)
      (spectrum ℝ X) := ContinuousOn.mul continuousOn_const hcinv
  have hcsub : ContinuousOn (fun x : ℝ => (h * Real.sqrt P) * (Real.sqrt x)⁻¹ - h)
      (spectrum ℝ X) := ContinuousOn.sub hcmul continuousOn_const
  have hfg : ∀ x ∈ spectrum ℝ X,
      a + h * (Real.sqrt P / Real.sqrt a - 1)
        ≤ x + ((h * Real.sqrt P) * (Real.sqrt x)⁻¹ - h) := by
    intro x hx
    have := euler_lower_scalar ha hP hPQ hh hhE (hspec x hx)
    linarith [this]
  have hcont1 : ContinuousOn (fun _ : ℝ => a + h * (Real.sqrt P / Real.sqrt a - 1))
      (spectrum ℝ X) := by fun_prop
  have hcont2 : ContinuousOn
      (fun x : ℝ => x + ((h * Real.sqrt P) * (Real.sqrt x)⁻¹ - h)) (spectrum ℝ X) :=
    ContinuousOn.add continuousOn_id hcsub
  have hmono := cfc_mono (R := ℝ) (a := X) hfg hcont1 hcont2
  have hsq : cfc Real.sqrt X = CFC.sqrt X := by
    rw [CFC.sqrt_eq_real_sqrt X hX.nonneg, cfcₙ_eq_cfc]
  have hL : cfc (fun _ : ℝ => a + h * (Real.sqrt P / Real.sqrt a - 1)) X
      = (a + h * (Real.sqrt P / Real.sqrt a - 1)) • (1 : A) := by
    rw [cfc_const _ X, Algebra.algebraMap_eq_smul_one]
  have hR : cfc (fun x : ℝ => x + ((h * Real.sqrt P) * (Real.sqrt x)⁻¹ - h)) X
      = X + (h * Real.sqrt P) • (X ^ (-(1/2) : ℝ)) - h • (1 : A) := by
    rw [cfc_add X (fun x : ℝ => x)
        (fun x : ℝ => (h * Real.sqrt P) * (Real.sqrt x)⁻¹ - h) continuousOn_id hcsub,
      cfc_id' ℝ X,
      cfc_sub (fun x : ℝ => (h * Real.sqrt P) * (Real.sqrt x)⁻¹) (fun _ : ℝ => h) X
        hcmul continuousOn_const,
      cfc_const_mul (h * Real.sqrt P) (fun x : ℝ => (Real.sqrt x)⁻¹) X hcinv,
      cfc_inv Real.sqrt X hne, hsq, CFC.sqrt_eq_rpow, ringInverse_rpow_half hX,
      cfc_const _ X, Algebra.algebraMap_eq_smul_one]
    abel
  rwa [hL, hR] at hmono

/-- The continuous functional calculus form of the upper inward estimate. -/
theorem euler_upper_le_smul_one {X : A} (hX : IsStrictlyPositive X) {a b Q h : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hQ : 0 < Q) (hh : 0 < h)
    (hhE : h * Real.sqrt Q ≤ 2 * a * Real.sqrt a)
    (hXa : a • (1 : A) ≤ X) (hXb : X ≤ b • (1 : A)) :
    X + (h * Real.sqrt Q) • (X ^ (-(1/2) : ℝ)) - h • (1 : A)
      ≤ (b + h * (Real.sqrt Q / Real.sqrt b - 1)) • (1 : A) := by
  have hXsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ X, a ≤ x := by
    rw [← algebraMap_le_iff_le_spectrum (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXa
  have hspecb : ∀ x ∈ spectrum ℝ X, x ≤ b := by
    rw [← le_algebraMap_iff_spectrum_le (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXb
  have hne : ∀ x ∈ spectrum ℝ X, Real.sqrt x ≠ 0 := fun x hx =>
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le ha (hspec x hx)))
  have hcinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ X) :=
    ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) hne
  have hcmul : ContinuousOn (fun x : ℝ => (h * Real.sqrt Q) * (Real.sqrt x)⁻¹)
      (spectrum ℝ X) := ContinuousOn.mul continuousOn_const hcinv
  have hcsub : ContinuousOn (fun x : ℝ => (h * Real.sqrt Q) * (Real.sqrt x)⁻¹ - h)
      (spectrum ℝ X) := ContinuousOn.sub hcmul continuousOn_const
  have hfg : ∀ x ∈ spectrum ℝ X,
      x + ((h * Real.sqrt Q) * (Real.sqrt x)⁻¹ - h)
        ≤ b + h * (Real.sqrt Q / Real.sqrt b - 1) := by
    intro x hx
    have := euler_upper_scalar ha hab hQ hh hhE (hspec x hx) (hspecb x hx)
    linarith [this]
  have hcont2 : ContinuousOn (fun _ : ℝ => b + h * (Real.sqrt Q / Real.sqrt b - 1))
      (spectrum ℝ X) := by fun_prop
  have hcont1 : ContinuousOn
      (fun x : ℝ => x + ((h * Real.sqrt Q) * (Real.sqrt x)⁻¹ - h)) (spectrum ℝ X) :=
    ContinuousOn.add continuousOn_id hcsub
  have hmono := cfc_mono (R := ℝ) (a := X) hfg hcont1 hcont2
  have hsq : cfc Real.sqrt X = CFC.sqrt X := by
    rw [CFC.sqrt_eq_real_sqrt X hX.nonneg, cfcₙ_eq_cfc]
  have hR : cfc (fun _ : ℝ => b + h * (Real.sqrt Q / Real.sqrt b - 1)) X
      = (b + h * (Real.sqrt Q / Real.sqrt b - 1)) • (1 : A) := by
    rw [cfc_const _ X, Algebra.algebraMap_eq_smul_one]
  have hL : cfc (fun x : ℝ => x + ((h * Real.sqrt Q) * (Real.sqrt x)⁻¹ - h)) X
      = X + (h * Real.sqrt Q) • (X ^ (-(1/2) : ℝ)) - h • (1 : A) := by
    rw [cfc_add X (fun x : ℝ => x)
        (fun x : ℝ => (h * Real.sqrt Q) * (Real.sqrt x)⁻¹ - h) continuousOn_id hcsub,
      cfc_id' ℝ X,
      cfc_sub (fun x : ℝ => (h * Real.sqrt Q) * (Real.sqrt x)⁻¹) (fun _ : ℝ => h) X
        hcmul continuousOn_const,
      cfc_const_mul (h * Real.sqrt Q) (fun x : ℝ => (Real.sqrt x)⁻¹) X hcinv,
      cfc_inv Real.sqrt X hne, hsq, CFC.sqrt_eq_rpow, ringInverse_rpow_half hX,
      cfc_const _ X, Algebra.algebraMap_eq_smul_one]
    abel
  rwa [hL, hR] at hmono

/-! ### The trapping lemma -/

/-- **Lemma 4.12 (Kim–Mer–Pálfia), uniform trapping.**  For all small enough steps the
normalized resolvent maps the Loewner interval `[(α/2)·1, (2β)·1]` into itself. -/
theorem exists_trapping_resolvent {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ X : A, IsStrictlyPositive X →
      (α / 2) • (1 : A) ≤ X → X ≤ (2 * β) • (1 : A) →
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ∃ Y : A, IsSelfAdjoint Y ∧ IsStrictlyPositive Y
          ∧ (α / 2) • (1 : A) ≤ Y ∧ Y ≤ (2 * β) • (1 : A)
          ∧ h • wassField s w Av Y + wassG Y X = 0 := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hα2 : (0 : ℝ) < α / 2 := by linarith
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  have hab : α / 2 ≤ 2 * β := by linarith
  have hsa2 : (0 : ℝ) < Real.sqrt (α / 2) := Real.sqrt_pos.mpr hα2
  have hsb2 : (0 : ℝ) < Real.sqrt (2 * β) := Real.sqrt_pos.mpr hβ2
  have hsb : (0 : ℝ) < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hAα' : ∀ i ∈ s, (α / 2) • (1 : A) ≤ Av i := fun i hi =>
    le_trans (smul_one_le_smul_one_of_le (by linarith)) (hAα i hi)
  have hAβ' : ∀ i ∈ s, Av i ≤ (2 * β) • (1 : A) := fun i hi =>
    le_trans (hAβ i hi) (smul_one_le_smul_one_of_le (by linarith))
  obtain ⟨hloc, Cloc, hloc0, hC0, hres⟩ :=
    exists_resolvent_step (A := A) (s := s) (w := w) (Av := Av) hα2 hab hw hwsum hA hAα' hAβ'
  -- the two inward margins
  obtain ⟨mm, hmmdef⟩ : ∃ m : ℝ, m = Real.sqrt α / Real.sqrt (α / 2) - 1 := ⟨_, rfl⟩
  obtain ⟨mp, hmpdef⟩ : ∃ m : ℝ, m = 1 - Real.sqrt β / Real.sqrt (2 * β) := ⟨_, rfl⟩
  have hmm0 : 0 < mm := by
    rw [hmmdef, sub_pos, lt_div_iff₀ hsa2, one_mul]
    exact Real.sqrt_lt_sqrt hα2.le (by linarith)
  have hmp0 : 0 < mp := by
    rw [hmpdef, sub_pos, div_lt_one hsb2]
    exact Real.sqrt_lt_sqrt hβ.le (by linarith)
  obtain ⟨hE, hEdef⟩ : ∃ e : ℝ, e = (2 * (α / 2) * Real.sqrt (α / 2)) / Real.sqrt β := ⟨_, rfl⟩
  have hE0 : 0 < hE := by rw [hEdef]; positivity
  refine ⟨min (min hloc hE) (min (mm / (Cloc + 1)) (mp / (Cloc + 1))), ?_, ?_⟩
  · exact lt_min (lt_min hloc0 hE0) (lt_min (by positivity) (by positivity))
  intro X hX hXα hXβ h hh hh0
  have hhloc : h ≤ hloc := le_trans hh0 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhE : h ≤ hE := le_trans hh0 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhm : h ≤ mm / (Cloc + 1) := le_trans hh0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhp : h ≤ mp / (Cloc + 1) := le_trans hh0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hhEs : h * Real.sqrt β ≤ 2 * (α / 2) * Real.sqrt (α / 2) := by
    rw [hEdef, le_div_iff₀ hsb] at hhE
    exact hhE
  obtain ⟨Y, hYsa, hYpos, -, -, hYeq, hYnorm⟩ := hres X hX hXα hXβ h hh hhloc
  -- the Euler map is inside with a margin
  obtain ⟨hlow, hupp⟩ := neg_wassField_Icc hX hα hβ hw hwsum hA hAα hAβ
  have hEuler : X - h • wassField s w Av X = X + h • (-wassField s w Av X) := by
    rw [smul_neg]; abel_nf
  have hlow2 : (α / 2 + h * mm) • (1 : A) ≤ X - h • wassField s w Av X := by
    have h1 := smul_one_le_euler_lower hX hα2 hα hαβ hh hhEs hXα
    have h2 : X + (h * Real.sqrt α) • (X ^ (-(1/2) : ℝ)) - h • (1 : A)
        = X + h • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1) := by
      rw [smul_sub, smul_smul]; abel_nf
    rw [h2] at h1
    have h3 : X + h • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
        ≤ X + h • (-wassField s w Av X) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hlow hh.le) X
    rw [hEuler, hmmdef]
    exact le_trans h1 h3
  have hupp2 : X - h • wassField s w Av X ≤ (2 * β - h * mp) • (1 : A) := by
    have h1 := euler_upper_le_smul_one hX hα2 hab hβ hh hhEs hXα hXβ
    have h2 : X + (h * Real.sqrt β) • (X ^ (-(1/2) : ℝ)) - h • (1 : A)
        = X + h • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) := by
      rw [smul_sub, smul_smul]; abel_nf
    rw [h2] at h1
    have h3 : X + h • (-wassField s w Av X)
        ≤ X + h • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hupp hh.le) X
    rw [hEuler, hmpdef]
    have h4 : (2 * β + h * (Real.sqrt β / Real.sqrt (2 * β) - 1))
        = 2 * β - h * (1 - Real.sqrt β / Real.sqrt (2 * β)) := by ring
    rw [← h4]
    exact le_trans h3 h1
  -- the resolvent inherits the bounds
  have hEsa : IsSelfAdjoint (X - h • wassField s w Av X) :=
    hX.isSelfAdjoint.sub (IsSelfAdjoint.smul (star_trivial h) (isSelfAdjoint_wassField hX))
  have hdsa : IsSelfAdjoint (Y - (X - h • wassField s w Av X)) := hYsa.sub hEsa
  have hmargin : Cloc * (h * h) ≤ h * mm := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < Cloc + 1)] at hhm
    nlinarith [hhm, hh.le, hC0]
  have hmarginp : Cloc * (h * h) ≤ h * mp := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < Cloc + 1)] at hhp
    nlinarith [hhp, hh.le, hC0]
  refine ⟨Y, hYsa, hYpos, ?_, ?_, hYeq⟩
  · have h1 := smul_one_le_of_norm_sub_le hdsa hYnorm hlow2
    refine le_trans (smul_one_le_smul_one_of_le ?_) h1
    linarith [hmargin]
  · have h1 := le_smul_one_of_norm_sub_le hdsa hYnorm hupp2
    refine le_trans h1 (smul_one_le_smul_one_of_le ?_)
    linarith [hmarginp]

/-- **Corollary 4.13 (Kim–Mer–Pálfia), freedom of resolvents.**  Any map that agrees with the
explicit Euler step to second order — however it is produced — leaves the Loewner interval
`[(α/2)·1, (2β)·1]` invariant for all small steps. -/
theorem mem_Icc_of_euler_close {α β C : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hC : 0 ≤ C)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ X Y : A, IsStrictlyPositive X →
      (α / 2) • (1 : A) ≤ X → X ≤ (2 * β) • (1 : A) → IsSelfAdjoint Y →
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ‖Y - (X - h • wassField s w Av X)‖ ≤ C * (h * h) →
        (α / 2) • (1 : A) ≤ Y ∧ Y ≤ (2 * β) • (1 : A) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hα2 : (0 : ℝ) < α / 2 := by linarith
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  have hab : α / 2 ≤ 2 * β := by linarith
  have hsa2 : (0 : ℝ) < Real.sqrt (α / 2) := Real.sqrt_pos.mpr hα2
  have hsb2 : (0 : ℝ) < Real.sqrt (2 * β) := Real.sqrt_pos.mpr hβ2
  have hsb : (0 : ℝ) < Real.sqrt β := Real.sqrt_pos.mpr hβ
  obtain ⟨mm, hmmdef⟩ : ∃ m : ℝ, m = Real.sqrt α / Real.sqrt (α / 2) - 1 := ⟨_, rfl⟩
  obtain ⟨mp, hmpdef⟩ : ∃ m : ℝ, m = 1 - Real.sqrt β / Real.sqrt (2 * β) := ⟨_, rfl⟩
  have hmm0 : 0 < mm := by
    rw [hmmdef, sub_pos, lt_div_iff₀ hsa2, one_mul]
    exact Real.sqrt_lt_sqrt hα2.le (by linarith)
  have hmp0 : 0 < mp := by
    rw [hmpdef, sub_pos, div_lt_one hsb2]
    exact Real.sqrt_lt_sqrt hβ.le (by linarith)
  obtain ⟨hE, hEdef⟩ : ∃ e : ℝ, e = (2 * (α / 2) * Real.sqrt (α / 2)) / Real.sqrt β := ⟨_, rfl⟩
  have hE0 : 0 < hE := by rw [hEdef]; positivity
  refine ⟨min hE (min (mm / (C + 1)) (mp / (C + 1))), ?_, ?_⟩
  · exact lt_min hE0 (lt_min (by positivity) (by positivity))
  intro X Y hX hXα hXβ hYsa h hh hh0 hclose
  have hhE : h ≤ hE := le_trans hh0 (min_le_left _ _)
  have hhm : h ≤ mm / (C + 1) := le_trans hh0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhp : h ≤ mp / (C + 1) := le_trans hh0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hhEs : h * Real.sqrt β ≤ 2 * (α / 2) * Real.sqrt (α / 2) := by
    rw [hEdef, le_div_iff₀ hsb] at hhE
    exact hhE
  obtain ⟨hlow, hupp⟩ := neg_wassField_Icc hX hα hβ hw hwsum hA hAα hAβ
  have hEuler : X - h • wassField s w Av X = X + h • (-wassField s w Av X) := by
    rw [smul_neg]; abel_nf
  have hlow2 : (α / 2 + h * mm) • (1 : A) ≤ X - h • wassField s w Av X := by
    have h1 := smul_one_le_euler_lower hX hα2 hα hαβ hh hhEs hXα
    have h2 : X + (h * Real.sqrt α) • (X ^ (-(1/2) : ℝ)) - h • (1 : A)
        = X + h • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1) := by
      rw [smul_sub, smul_smul]; abel_nf
    rw [h2] at h1
    have h3 : X + h • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
        ≤ X + h • (-wassField s w Av X) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hlow hh.le) X
    rw [hEuler, hmmdef]
    exact le_trans h1 h3
  have hupp2 : X - h • wassField s w Av X ≤ (2 * β - h * mp) • (1 : A) := by
    have h1 := euler_upper_le_smul_one hX hα2 hab hβ hh hhEs hXα hXβ
    have h2 : X + (h * Real.sqrt β) • (X ^ (-(1/2) : ℝ)) - h • (1 : A)
        = X + h • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) := by
      rw [smul_sub, smul_smul]; abel_nf
    rw [h2] at h1
    have h3 : X + h • (-wassField s w Av X)
        ≤ X + h • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hupp hh.le) X
    rw [hEuler, hmpdef]
    have h4 : (2 * β + h * (Real.sqrt β / Real.sqrt (2 * β) - 1))
        = 2 * β - h * (1 - Real.sqrt β / Real.sqrt (2 * β)) := by ring
    rw [← h4]
    exact le_trans h3 h1
  have hEsa : IsSelfAdjoint (X - h • wassField s w Av X) :=
    hX.isSelfAdjoint.sub (IsSelfAdjoint.smul (star_trivial h) (isSelfAdjoint_wassField hX))
  have hdsa : IsSelfAdjoint (Y - (X - h • wassField s w Av X)) := hYsa.sub hEsa
  have hmargin : C * (h * h) ≤ h * mm := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < C + 1)] at hhm
    nlinarith [hhm, hh.le, hC]
  have hmarginp : C * (h * h) ≤ h * mp := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < C + 1)] at hhp
    nlinarith [hhp, hh.le, hC]
  constructor
  · have h1 := smul_one_le_of_norm_sub_le hdsa hclose hlow2
    refine le_trans (smul_one_le_smul_one_of_le ?_) h1
    linarith [hmargin]
  · have h1 := le_smul_one_of_norm_sub_le hdsa hclose hupp2
    refine le_trans h1 (smul_one_le_smul_one_of_le ?_)
    linarith [hmarginp]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
