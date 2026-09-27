import Mathlib

/-!
# The Volterra convolution algebra on the real line

For functions on `ℝ` put `(f ⋆ g)(t) = ∫₀^t f(t - s) g(s) ds`, the integral being oriented, so
negative `t` are allowed.  For continuous functions this product is continuous, commutative,
bilinear and associative (Fubini on the triangle `0 ≤ s ≤ u ≤ t`, and reflection `t ↦ -t` for
negative `t`); multiplication by `t` is a derivation, and `e^{at}` twists multiplicatively.
-/

open MeasureTheory Set intervalIntegral Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The oriented Volterra convolution `(f ⋆ g)(t) = ∫₀^t f(t - s) g(s) ds`. -/
def volterraConv (f g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, f (t - s) * g s

variable {f g h : ℝ → ℝ}

theorem continuous_volterraConv (hf : Continuous f) (hg : Continuous g) :
    Continuous (volterraConv f g) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t s => f (t - s) * g s) (by fun_prop) continuous_id

theorem volterraConv_comm (f g : ℝ → ℝ) (t : ℝ) : volterraConv f g t = volterraConv g f t := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
    (fun s => g (t - s) * f s) t
  simp only [sub_zero, sub_self, sub_sub_cancel] at h
  rw [volterraConv, volterraConv, ← h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

theorem volterraConv_comm' (f g : ℝ → ℝ) : volterraConv f g = volterraConv g f :=
  funext (volterraConv_comm f g)

theorem volterraConv_add_right (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (t : ℝ) : volterraConv f (g + h) t = volterraConv f g t + volterraConv f h t := by
  rw [volterraConv, volterraConv, volterraConv, ← intervalIntegral.integral_add
    ((by fun_prop : Continuous fun s => f (t - s) * g s).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s => f (t - s) * h s).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Pi.add_apply]; ring

theorem volterraConv_smul_right (c : ℝ) (f g : ℝ → ℝ) (t : ℝ) :
    volterraConv f (fun s => c * g s) t = c * volterraConv f g t := by
  rw [volterraConv, volterraConv, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

theorem volterraConv_smul_left (c : ℝ) (f g : ℝ → ℝ) (t : ℝ) :
    volterraConv (fun s => c * f s) g t = c * volterraConv f g t := by
  rw [volterraConv, volterraConv, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

theorem volterraConv_neg_left (f g : ℝ → ℝ) (t : ℝ) :
    volterraConv (fun s => -f s) g t = -volterraConv f g t := by
  have := volterraConv_smul_left (-1) f g t
  simpa using this

theorem volterraConv_neg_right (f g : ℝ → ℝ) (t : ℝ) :
    volterraConv f (fun s => -g s) t = -volterraConv f g t := by
  have := volterraConv_smul_right (-1) f g t
  simpa using this

theorem volterraConv_sub_right (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (t : ℝ) : volterraConv f (fun s => g s - h s) t = volterraConv f g t - volterraConv f h t := by
  rw [volterraConv, volterraConv, volterraConv, ← intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun s => f (t - s) * g s).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s => f (t - s) * h s).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- Multiplication by `t` is a derivation: `t (f ⋆ g) = (t f) ⋆ g + f ⋆ (t g)`. -/
theorem mul_volterraConv (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    t * volterraConv f g t =
      volterraConv (fun s => s * f s) g t + volterraConv f (fun s => s * g s) t := by
  rw [volterraConv, volterraConv, volterraConv, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add
      ((by fun_prop : Continuous fun s => (t - s) * f (t - s) * g s).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => f (t - s) * (s * g s)).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- Exponential twist: `e^{at} (f ⋆ g)(t) = ((e^{a·} f) ⋆ (e^{a·} g))(t)`. -/
theorem exp_mul_volterraConv (a : ℝ) (f g : ℝ → ℝ) (t : ℝ) :
    Real.exp (a * t) * volterraConv f g t =
      volterraConv (fun s => Real.exp (a * s) * f s) (fun s => Real.exp (a * s) * g s) t := by
  rw [volterraConv, volterraConv, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have : Real.exp (a * t) = Real.exp (a * (t - s)) * Real.exp (a * s) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

/-- Reflection: `(f ⋆ g)(-t) = -((f ∘ neg) ⋆ (g ∘ neg))(t)`. -/
theorem volterraConv_neg (f g : ℝ → ℝ) (t : ℝ) :
    volterraConv f g (-t) = -volterraConv (fun s => f (-s)) (fun s => g (-s)) t := by
  rw [volterraConv, volterraConv]
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := t)
    (fun s => f (-t - s) * g s)
  simp only [neg_zero] at h
  rw [intervalIntegral.integral_symm, ← h]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring_nf

/-- Iterated integrals over the triangle `0 ≤ s ≤ u ≤ t` may be exchanged. -/
theorem intervalIntegral_triangle_swap_of_continuous {t : ℝ} (ht : 0 ≤ t) {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) :
    (∫ u in (0 : ℝ)..t, ∫ s in (0 : ℝ)..u, F u s) = ∫ s in (0 : ℝ)..t, ∫ u in s..t, F u s := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) t)
  let G : ℝ → ℝ → ℝ := fun u s => if s ≤ u then F u s else 0
  have hmeas : Measurable (Function.uncurry G) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst) hF.measurable measurable_const
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact
    (Icc (0 : ℝ) t ×ˢ Icc (0 : ℝ) t)).exists_bound_of_continuousOn hF.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0, 0) ⟨⟨le_rfl, ht⟩, ⟨le_rfl, ht⟩⟩)
  have hG : Integrable (Function.uncurry G) (μ.prod μ) := by
    refine (integrable_const C).mono' hmeas.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
      (Eventually.of_forall fun p hp => ?_)
    simp only [Function.uncurry, G]
    split_ifs
    · exact hC p ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
    · simp only [norm_zero]; exact hC0
  have hL : ∀ u ∈ Ioc (0 : ℝ) t, (∫ s in (0 : ℝ)..u, F u s) = ∫ s, G u s ∂μ := by
    intro u hu
    rw [intervalIntegral.integral_of_le hu.1.le]
    have hind : (fun s => G u s) = (Iic u).indicator (fun s => F u s) := by
      funext s; simp only [G, Set.indicator, mem_Iic]
    have hset : Ioc (0 : ℝ) t ∩ Iic u = Ioc 0 u := by
      ext s; simp only [mem_Ioc, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hu.2⟩, h2⟩
    rw [hind, setIntegral_indicator measurableSet_Iic, hset]
  have hR : ∀ s ∈ Ioc (0 : ℝ) t, (∫ u in s..t, F u s) = ∫ u, G u s ∂μ := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs.2, ← integral_Icc_eq_integral_Ioc]
    have hind : (fun u => G u s) = (Ici s).indicator (fun u => F u s) := by
      funext u; simp only [G, Set.indicator, mem_Ici]
    have hset : Ioc (0 : ℝ) t ∩ Ici s = Icc s t := by
      ext u; simp only [mem_Ioc, mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hs.1 h1, h2⟩, h1⟩
    rw [hind, setIntegral_indicator measurableSet_Ici, hset]
  calc (∫ u in (0 : ℝ)..t, ∫ s in (0 : ℝ)..u, F u s) = ∫ u, ∫ s, G u s ∂μ ∂μ := by
        rw [intervalIntegral.integral_of_le ht]
        exact setIntegral_congr_fun measurableSet_Ioc hL
    _ = ∫ s, ∫ u, G u s ∂μ ∂μ := integral_integral_swap hG
    _ = ∫ s in (0 : ℝ)..t, ∫ u in s..t, F u s := by
        rw [intervalIntegral.integral_of_le ht]
        exact (setIntegral_congr_fun measurableSet_Ioc hR).symm

theorem volterraConv_assoc_of_nonneg (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    {t : ℝ} (ht : 0 ≤ t) :
    volterraConv (volterraConv f g) h t = volterraConv f (volterraConv g h) t := by
  have hswap := intervalIntegral_triangle_swap_of_continuous ht
    (F := fun u s => f (t - u) * (g (u - s) * h s)) (by fun_prop)
  rw [volterraConv, volterraConv]
  simp only [volterraConv]
  rw [show (∫ u in (0 : ℝ)..t, f (t - u) * ∫ s in (0 : ℝ)..u, g (u - s) * h s) =
      ∫ u in (0 : ℝ)..t, ∫ s in (0 : ℝ)..u, f (t - u) * (g (u - s) * h s) by
    refine intervalIntegral.integral_congr fun u _ => ?_
    exact (intervalIntegral.integral_const_mul _ _).symm, hswap]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hsub := intervalIntegral.integral_comp_add_right (a := 0) (b := t - s)
    (fun u => f (t - u) * (g (u - s) * h s)) s
  simp only [zero_add, sub_add_cancel] at hsub
  rw [← hsub, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun r _ => ?_
  ring_nf

/-- **Associativity** of the Volterra convolution of continuous functions. -/
theorem volterraConv_assoc (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (t : ℝ) :
    volterraConv (volterraConv f g) h t = volterraConv f (volterraConv g h) t := by
  rcases le_total 0 t with ht | ht
  · exact volterraConv_assoc_of_nonneg hf hg hh ht
  · obtain ⟨u, rfl⟩ : ∃ u, t = -u := ⟨-t, by ring⟩
    have hu : 0 ≤ u := by linarith
    have hf' : Continuous fun s => f (-s) := hf.comp continuous_neg
    have hg' : Continuous fun s => g (-s) := hg.comp continuous_neg
    have hh' : Continuous fun s => h (-s) := hh.comp continuous_neg
    have key := volterraConv_assoc_of_nonneg hf' hg' hh' hu
    have e1 : (fun s => volterraConv f g (-s)) =
        fun s => -volterraConv (fun s => f (-s)) (fun s => g (-s)) s :=
      funext fun s => volterraConv_neg f g s
    have e2 : (fun s => volterraConv g h (-s)) =
        fun s => -volterraConv (fun s => g (-s)) (fun s => h (-s)) s :=
      funext fun s => volterraConv_neg g h s
    rw [volterraConv_neg, volterraConv_neg, e1, e2, volterraConv_neg_left, volterraConv_neg_right,
      key]

/-! ## Bounds, uniqueness and series -/

theorem abs_volterraConv_le_of_nonneg {A B : ℝ} {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc 0 t, |f s| ≤ A)
    (hB : ∀ s ∈ Icc 0 t, |g s| ≤ B * s ^ n / n.factorial) :
    |volterraConv f g t| ≤ A * B * t ^ (n + 1) / (n + 1).factorial := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 ⟨le_rfl, ht⟩)
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc 0 t →
      ‖f (t - s) * g s‖ ≤ A * (B * s ^ n / n.factorial) := by
    refine Eventually.of_forall fun s hs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hA _ ⟨by linarith [hs.2], by linarith [hs.1]⟩) (hB s ⟨hs.1.le, hs.2⟩)
      (abs_nonneg _) hA0
  have h := intervalIntegral.norm_integral_le_of_norm_le ht hbound
    ((by fun_prop : Continuous fun s : ℝ => A * (B * s ^ n / n.factorial)).intervalIntegrable _ _)
  rw [Real.norm_eq_abs] at h
  refine (le_of_le_of_eq h ?_)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `|(f ⋆ g)(t)| ≤ A B |t|^{n+1}/(n+1)!` when `|f| ≤ A` and `|g(s)| ≤ B |s|^n/n!` for `|s| ≤ |t|`. -/
theorem abs_volterraConv_le {A B : ℝ} {n : ℕ} {t : ℝ}
    (hA : ∀ s, |s| ≤ |t| → |f s| ≤ A) (hB : ∀ s, |s| ≤ |t| → |g s| ≤ B * |s| ^ n / n.factorial) :
    |volterraConv f g t| ≤ A * B * |t| ^ (n + 1) / (n + 1).factorial := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    refine abs_volterraConv_le_of_nonneg ht (fun s hs => hA s ?_) (fun s hs => ?_)
    · rw [abs_of_nonneg hs.1, abs_of_nonneg ht]; exact hs.2
    · have := hB s (by rw [abs_of_nonneg hs.1, abs_of_nonneg ht]; exact hs.2)
      rwa [abs_of_nonneg hs.1] at this
  · obtain ⟨u, rfl⟩ : ∃ u, t = -u := ⟨-t, by ring⟩
    have hu : 0 ≤ u := by linarith
    rw [volterraConv_neg, abs_neg, abs_neg, abs_of_nonneg hu]
    refine abs_volterraConv_le_of_nonneg hu (fun s hs => hA (-s) ?_) (fun s hs => ?_)
    · rw [abs_neg, abs_neg, abs_of_nonneg hs.1, abs_of_nonneg hu]; exact hs.2
    · have := hB (-s) (by rw [abs_neg, abs_neg, abs_of_nonneg hs.1, abs_of_nonneg hu]; exact hs.2)
      rwa [abs_neg, abs_of_nonneg hs.1] at this

/-- An exponential Volterra kernel is injective: `e^{a·} ⋆ g = 0` forces `g = 0`. -/
theorem eq_zero_of_volterraConv_exp_eq_zero {a : ℝ} (hg : Continuous g)
    (h0 : ∀ t, volterraConv (fun s => Real.exp (a * s)) g t = 0) : g = 0 := by
  funext t
  have hG : ∀ u, (∫ s in (0 : ℝ)..u, Real.exp (-(a * s)) * g s) = 0 := by
    intro u
    have h := h0 u
    rw [volterraConv] at h
    have e : (∫ s in (0 : ℝ)..u, Real.exp (a * (u - s)) * g s) =
        Real.exp (a * u) * ∫ s in (0 : ℝ)..u, Real.exp (-(a * s)) * g s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [← mul_assoc, ← Real.exp_add]; ring_nf
    rw [e] at h
    exact (mul_eq_zero.mp h).resolve_left (Real.exp_pos _).ne'
  have hd : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, Real.exp (-(a * s)) * g s)
      (Real.exp (-(a * t)) * g t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((by fun_prop : Continuous fun s => Real.exp (-(a * s)) * g s).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => Real.exp (-(a * s)) * g s).stronglyMeasurableAtFilter _ _)
      (by fun_prop : Continuous fun s => Real.exp (-(a * s)) * g s).continuousAt
  have hfun : (fun u => ∫ s in (0 : ℝ)..u, Real.exp (-(a * s)) * g s) = fun _ => 0 := funext hG
  rw [hfun] at hd
  have := hd.unique (hasDerivAt_const t (0 : ℝ))
  simpa [(Real.exp_pos _).ne'] using this

theorem eq_zero_of_mul_eq_volterraConv_of_nonneg {k : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hk : Continuous k) (hf : Continuous f) (h : ∀ t, 0 ≤ t → c * f t = volterraConv k f t)
    {t : ℝ} (ht : 0 ≤ t) : f t = 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc 0 t))
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hk.continuousOn (s := Icc 0 t))
  have hc0 : 0 < |c| := abs_pos.2 hc
  have hind : ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) t,
      |f s| ≤ M * (A / |c|) ^ n * s ^ n / n.factorial := by
    intro n
    induction n with
    | zero => intro s hs; simpa [Real.norm_eq_abs] using hM s hs
    | succ n ih =>
      intro s hs
      have hconv := abs_volterraConv_le_of_nonneg (f := k) (g := f) (A := A)
        (B := M * (A / |c|) ^ n) (n := n) hs.1
        (fun r hr => by
          have := hA r ⟨hr.1, hr.2.trans hs.2⟩; rwa [Real.norm_eq_abs] at this)
        (fun r hr => ih r ⟨hr.1, hr.2.trans hs.2⟩)
      have hfs : |f s| = |volterraConv k f s| / |c| := by
        rw [← h s hs.1, abs_mul, mul_div_cancel_left₀ _ hc0.ne']
      rw [hfs, div_le_iff₀ hc0]
      refine hconv.trans (le_of_eq ?_)
      have hc' : |c| ≠ 0 := hc0.ne'
      rw [Nat.factorial_succ, pow_succ, pow_succ, div_pow]
      push_cast
      field_simp
  have hlim : Tendsto (fun n : ℕ => M * (((A / |c|) * t) ^ n / n.factorial)) atTop (nhds (M * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop ((A / |c|) * t)).const_mul M
  rw [mul_zero] at hlim
  have hle : ∀ n : ℕ, |f t| ≤ M * (((A / |c|) * t) ^ n / n.factorial) := fun n => by
    have := hind n t ⟨ht, le_rfl⟩
    rw [mul_pow]; exact this.trans (le_of_eq (by ring))
  have h0 : |f t| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hle)
  exact abs_nonpos_iff.mp h0

/-- **Homogeneous Volterra equations of the second kind** have only the zero solution. -/
theorem eq_zero_of_mul_eq_volterraConv {k : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0) (hk : Continuous k)
    (hf : Continuous f) (h : ∀ t, c * f t = volterraConv k f t) : f = 0 := by
  funext t
  rcases le_total 0 t with ht | ht
  · exact eq_zero_of_mul_eq_volterraConv_of_nonneg hc hk hf (fun t _ => h t) ht
  · obtain ⟨u, rfl⟩ : ∃ u, t = -u := ⟨-t, by ring⟩
    have hu : 0 ≤ u := by linarith
    refine eq_zero_of_mul_eq_volterraConv_of_nonneg (k := fun s => -k (-s)) (f := fun s => f (-s))
      hc (hk.comp continuous_neg).neg (hf.comp continuous_neg) (fun s _ => ?_) hu
    rw [h (-s), volterraConv_neg, volterraConv_neg_left]

/-- Convolution against a locally uniformly summable series is termwise. -/
theorem volterraConv_tsum {G : ℕ → ℝ → ℝ} (hf : Continuous f) (hG : ∀ m, Continuous (G m))
    {B : ℕ → ℝ} (hB : Summable B) {t : ℝ} (hbound : ∀ m s, |s| ≤ |t| → |G m s| ≤ B m) :
    volterraConv f (fun s => ∑' m, G m s) t = ∑' m, volterraConv f (G m) t := by
  refine (intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun m s => f (t - s) * G m s) (fun m s => |f (t - s)| * B m)
    (fun m => ((by fun_prop : Continuous fun s => f (t - s)).mul (hG m)).aestronglyMeasurable)
    (fun m => Eventually.of_forall fun s hs => ?_)
    (Eventually.of_forall fun s _ => hB.mul_left _) ?_
    (Eventually.of_forall fun s hs => ?_)).tsum_eq.symm
  · rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left (hbound m s ?_) (abs_nonneg _)
    rcases le_total 0 t with ht | ht
    · rw [uIoc_of_le ht] at hs; rw [abs_of_pos hs.1, abs_of_nonneg ht]; exact hs.2
    · rw [uIoc_of_ge ht] at hs; rw [abs_of_nonpos hs.2, abs_of_nonpos ht]; linarith [hs.1]
  · simp only [tsum_mul_left]
    exact ((by fun_prop : Continuous fun s => |f (t - s)|).mul continuous_const).intervalIntegrable _ _
  · have hsum : Summable fun m => G m s := by
      refine Summable.of_norm_bounded hB fun m => ?_
      rw [Real.norm_eq_abs]
      refine hbound m s ?_
      rcases le_total 0 t with ht | ht
      · rw [uIoc_of_le ht] at hs; rw [abs_of_pos hs.1, abs_of_nonneg ht]; exact hs.2
      · rw [uIoc_of_ge ht] at hs; rw [abs_of_nonpos hs.2, abs_of_nonpos ht]; linarith [hs.1]
    exact hsum.hasSum.mul_left (f (t - s))

/-! ## Laplace transform of a convolution -/

theorem setIntegral_Ioi_comp_add_right_complex (F : ℝ → ℂ) (u : ℝ) :
    ∫ r in Ioi (0 : ℝ), F (r + u) = ∫ t in Ioi u, F t := by
  have h := (measurePreserving_add_right volume u).setIntegral_preimage_emb
    (measurableEmbedding_addRight u) F (Ioi u)
  have hpre : (fun x : ℝ => x + u) ⁻¹' Ioi u = Ioi 0 := by ext x; simp
  rwa [hpre] at h

/-- **Laplace transform of a Volterra convolution.**  For continuous `f, g` with
`∫₀^∞ e^{-σt}|f|, ∫₀^∞ e^{-σt}|g| < ∞` (`σ = Re s`),
`∫₀^∞ e^{-st} (f ⋆ g)(t) dt = (∫₀^∞ e^{-st} f)(∫₀^∞ e^{-st} g)`. -/
theorem integral_Ioi_cexp_mul_volterraConv (hf : Continuous f) (hg : Continuous g) {s : ℂ}
    (hfi : IntegrableOn (fun t => Real.exp (-(s.re * t)) * |f t|) (Ioi 0))
    (hgi : IntegrableOn (fun t => Real.exp (-(s.re * t)) * |g t|) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (volterraConv f g t : ℂ)) =
      (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (f t : ℂ)) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (g t : ℂ) := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let K : ℝ → ℝ → ℂ := fun t u =>
    if u ≤ t then Complex.exp (-(s * t)) * ((f (t - u) : ℂ) * (g u : ℂ)) else 0
  have hnorm : ∀ t u : ℝ, ‖Complex.exp (-(s * t)) * ((f (t - u) : ℂ) * (g u : ℂ))‖ =
      (Real.exp (-(s.re * (t - u))) * |f (t - u)|) * (Real.exp (-(s.re * u)) * |g u|) := by
    intro t u
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hre : (-(s * (t : ℂ))).re = -(s.re * t) := by simp
    rw [hre, show -(s.re * t) = -(s.re * (t - u)) + -(s.re * u) by ring, Real.exp_add]
    ring
  have hmeas : Measurable (Function.uncurry K) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      ((by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp (-(s * p.1)) * ((f (p.1 - p.2) : ℂ) * (g p.2 : ℂ))).measurable)
      measurable_const
  -- shifted integrability of the `f`-factor
  have hshift : ∀ u, IntegrableOn (fun t => Real.exp (-(s.re * (t - u))) * |f (t - u)|) (Ici u) := by
    intro u
    have h1 : IntegrableOn (fun t => Real.exp (-(s.re * (t - u))) * |f (t - u)|) (Ioi u) := by
      have := (measurePreserving_add_right volume u).integrableOn_comp_preimage
        (measurableEmbedding_addRight u) (f := fun t => Real.exp (-(s.re * (t - u))) * |f (t - u)|)
        (s := Ioi u)
      have hpre : (fun x : ℝ => x + u) ⁻¹' Ioi u = Ioi 0 := by ext x; simp
      rw [hpre] at this
      refine this.mp ?_
      refine hfi.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
  have hK : Integrable (Function.uncurry K) (μ.prod μ) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_), ?_⟩
    · have hind : (fun t => Function.uncurry K (t, u)) = (Ici u).indicator
          (fun t => Complex.exp (-(s * t)) * ((f (t - u) : ℂ) * (g u : ℂ))) := by
        funext t; simp only [Function.uncurry, K, Set.indicator, mem_Ici]
      rw [hind, integrable_indicator_iff measurableSet_Ici]
      have hF : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * ((f (t - u) : ℂ) * (g u : ℂ)))
          (Ici u) := by
        refine ((hshift u).mul_const (Real.exp (-(s.re * u)) * |g u|)).mono' ?_
          (Eventually.of_forall fun t => by rw [hnorm])
        exact ((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (-(s * t)) * ((f (t - u) : ℂ) * (g u : ℂ))).aestronglyMeasurable)
      exact hF.mono_measure Measure.restrict_le_self
    · refine Integrable.congr (hgi.const_mul (∫ r in Ioi (0 : ℝ), Real.exp (-(s.re * r)) * |f r|)) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      have hu0 : (0 : ℝ) < u := hu
      have hind : (fun t => ‖Function.uncurry K (t, u)‖) = (Ici u).indicator
          (fun t => (Real.exp (-(s.re * (t - u))) * |f (t - u)|) *
            (Real.exp (-(s.re * u)) * |g u|)) := by
        funext t; simp only [Function.uncurry, K, Set.indicator, mem_Ici]
        split_ifs
        · rw [hnorm]
        · simp
      beta_reduce
      rw [hind, setIntegral_indicator measurableSet_Ici,
        show Ioi (0 : ℝ) ∩ Ici u = Ici u by
          ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
          · exact fun h => h.2
          · exact fun h => ⟨lt_of_lt_of_le hu0 h, h⟩,
        MeasureTheory.integral_mul_const, integral_Ici_eq_integral_Ioi]
      have := setIntegral_Ioi_comp_add_right_complex
        (fun t => ((Real.exp (-(s.re * (t - u))) * |f (t - u)| : ℝ) : ℂ)) u
      simp only [add_sub_cancel_right] at this
      have h2 : (∫ t in Ioi u, Real.exp (-(s.re * (t - u))) * |f (t - u)|) =
          ∫ r in Ioi (0 : ℝ), Real.exp (-(s.re * r)) * |f r| := by
        have h3 := (measurePreserving_add_right volume u).setIntegral_preimage_emb
          (measurableEmbedding_addRight u) (fun t => Real.exp (-(s.re * (t - u))) * |f (t - u)|)
          (Ioi u)
        have hpre : (fun x : ℝ => x + u) ⁻¹' Ioi u = Ioi 0 := by ext x; simp
        rw [hpre] at h3
        rw [← h3]
        simp
      rw [h2]
  have hL : ∀ t ∈ Ioi (0 : ℝ), Complex.exp (-(s * t)) * (volterraConv f g t : ℂ) =
      ∫ u, K t u ∂μ := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [volterraConv, intervalIntegral.integral_of_le ht0.le, ← integral_complex_ofReal,
      ← MeasureTheory.integral_const_mul]
    have hind : (fun u => K t u) = (Iic t).indicator
        (fun u => Complex.exp (-(s * t)) * ((f (t - u) : ℂ) * (g u : ℂ))) := by
      funext u; simp only [K, Set.indicator, mem_Iic]
    rw [hind, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
    rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    push_cast; ring
  have hR : ∀ u ∈ Ioi (0 : ℝ), (∫ t, K t u ∂μ) = (∫ r in Ioi (0 : ℝ), Complex.exp (-(s * r)) *
      (f r : ℂ)) * (Complex.exp (-(s * u)) * (g u : ℂ)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hind : (fun t => K t u) = (Ici u).indicator
        (fun t => Complex.exp (-(s * t)) * ((f (t - u) : ℂ) * (g u : ℂ))) := by
      funext t; simp only [K, Set.indicator, mem_Ici]
    rw [hind, setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici u = Ici u by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
        · exact fun h => h.2
        · exact fun h => ⟨lt_of_lt_of_le hu0 h, h⟩,
      integral_Ici_eq_integral_Ioi, ← setIntegral_Ioi_comp_add_right_complex,
      ← MeasureTheory.integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [add_sub_cancel_right]
    rw [show -(s * ((r + u : ℝ) : ℂ)) = -(s * r) + -(s * u) by push_cast; ring, Complex.exp_add]
    ring
  calc (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (volterraConv f g t : ℂ))
      = ∫ t, ∫ u, K t u ∂μ ∂μ := setIntegral_congr_fun measurableSet_Ioi hL
    _ = ∫ u, ∫ t, K t u ∂μ ∂μ := integral_integral_swap hK
    _ = ∫ u in Ioi (0 : ℝ), (∫ r in Ioi (0 : ℝ), Complex.exp (-(s * r)) * (f r : ℂ)) *
          (Complex.exp (-(s * u)) * (g u : ℂ)) := setIntegral_congr_fun measurableSet_Ioi hR
    _ = _ := MeasureTheory.integral_const_mul _ _

end

end GaloisForLFunctions.HTGeometry
