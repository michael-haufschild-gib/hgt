import GaloisForLFunctions.StripBochnerWeilForcing.CollectivePoleRepulsion

/-!
# Positive-definite vertical sections and complete monotonicity

Let `G` be holomorphic on a right half-plane `{a < Re s}` with `u ↦ Re G(σ + iu)` positive definite
for every `σ > a`. This module proves that every even derivative of `G` has positive-definite
vertical sections, so `G^{(2k)}(σ) ≥ 0` at every real point `σ > a`.

* Second differences `2φ(u) − φ(u + h) − φ(u − h)` of a positive-definite `φ` are positive definite
  (`isPosDef_secondDiff`): their quadratic form is that of `φ` at the doubled point set
  `{x_i, x_i + h}` with coefficients `(c, −c)`. Pointwise limits keep positive definiteness.
* For holomorphic `H`, `(2 Re H(w) − Re H(w + ih) − Re H(w − ih))/h² → Re H''(w)`
  (`tendsto_secondDiffQuotient_re`), since `h ↦ H(w + ih) + H(w − ih) − 2H(w) + H''(w)h²` has
  vanishing second derivative at `0`.
* Hence `u ↦ Re H''(σ + iu)` is positive definite whenever `u ↦ Re H(σ + iu)` is
  (`isPosDef_re_deriv_deriv_vertical`), and by induction every `G^{(2k)}` has positive-definite
  vertical sections (`isPosDef_re_iterate_deriv_two_mul`).
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.StripBochnerWeilForcing

open MultiplicativePositivityGeometry

/-! ## 1. Second differences and limits -/

/-- Second differences of a positive-definite function are positive definite. -/
theorem isPosDef_secondDiff {φ : ℝ → ℝ} (hφ : IsPosDef φ) (h : ℝ) :
    IsPosDef (fun u => 2 * φ u - φ (u + h) - φ (u - h)) := by
  intro n x c
  have H := hφ (n + n) (Fin.append x fun i => x i + h) (Fin.append c fun i => -c i)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right] at H
  have e : ∑ i, ∑ j, c i * c j * (2 * φ (x i - x j) - φ (x i - x j + h) - φ (x i - x j - h)) =
      (∑ i, ((∑ j, c i * c j * φ (x i - x j)) + ∑ j, c i * -c j * φ (x i - (x j + h)))) +
      ∑ i, ((∑ j, -c i * c j * φ (x i + h - x j)) +
        ∑ j, -c i * -c j * φ (x i + h - (x j + h))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : x i - (x j + h) = x i - x j - h := by ring
    have e2 : x i + h - x j = x i - x j + h := by ring
    have e3 : x i + h - (x j + h) = x i - x j := by ring
    rw [e1, e2, e3]
    ring
  rw [e]
  exact H

theorem isPosDef_const_mul {φ : ℝ → ℝ} (hφ : IsPosDef φ) {a : ℝ} (ha : 0 ≤ a) :
    IsPosDef (fun u => a * φ u) := by
  intro n x c
  have e : ∑ i, ∑ j, c i * c j * (a * φ (x i - x j)) =
      a * ∑ i, ∑ j, c i * c j * φ (x i - x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact mul_nonneg ha (hφ n x c)

/-- Pointwise limits of positive-definite functions are positive definite. -/
theorem isPosDef_of_tendsto {φ : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ} {l : Filter ℝ} [l.NeBot]
    (hψ : ∀ᶠ h in l, IsPosDef (ψ h)) (hlim : ∀ u, Tendsto (fun h => ψ h u) l (𝓝 (φ u))) :
    IsPosDef φ := by
  intro n x c
  have hT : Tendsto (fun h => ∑ i, ∑ j, c i * c j * ψ h (x i - x j)) l
      (𝓝 (∑ i, ∑ j, c i * c j * φ (x i - x j))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => (hlim _).const_mul _
  exact ge_of_tendsto hT (hψ.mono fun h hh => hh n x c)

theorem isPosDef_apply_zero_nonneg {φ : ℝ → ℝ} (hφ : IsPosDef φ) : 0 ≤ φ 0 := by
  have h := hφ 1 (fun _ => 0) (fun _ => 1)
  simpa using h

/-! ## 2. The vertical second-difference quotient -/

/-- The vertical derivative: `d/dr H(w + c r I) = H'(w + c r I) · cI`. -/
theorem hasDerivAt_vertical {H : ℂ → ℂ} {w c : ℂ} {t : ℝ}
    (hH : DifferentiableAt ℂ H (w + c * (t : ℂ) * I)) :
    HasDerivAt (fun r : ℝ => H (w + c * (r : ℂ) * I)) (deriv H (w + c * (t : ℂ) * I) * (c * I))
      t := by
  have hin : HasDerivAt (fun z : ℂ => w + c * z * I) (c * I) (t : ℂ) := by
    have h := (((hasDerivAt_id (t : ℂ)).const_mul c).mul_const I).const_add w
    simpa only [mul_one, id] using h
  exact (hH.hasDerivAt.comp (t : ℂ) hin).comp_ofReal


/-- `d/dr (r : ℂ)² = 2r`. -/
theorem hasDerivAt_ofReal_sq (t : ℝ) :
    HasDerivAt (fun r : ℝ => ((r : ℂ)) ^ 2) (2 * (t : ℂ)) t := by
  have h := (hasDerivAt_pow 2 (t : ℂ)).comp_ofReal
  simpa using h

/-- **The vertical second-difference quotient.** For `H` holomorphic on an open set containing the
vertical line through `w`, `(2 Re H(w) − Re H(w + ih) − Re H(w − ih))/h² → Re H''(w)` as `h → 0`. -/
theorem tendsto_secondDiffQuotient_re {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hH : DifferentiableOn ℂ H U) {w : ℂ} (hline : ∀ t : ℝ, w + (t : ℂ) * I ∈ U) :
    Tendsto (fun h : ℝ => (2 * (H w).re - (H (w + 1 * (h : ℂ) * I)).re -
        (H (w + (-1) * (h : ℂ) * I)).re) / h ^ 2) (𝓝[≠] 0) (𝓝 (deriv (deriv H) w).re) := by
  have hH1 : DifferentiableOn ℂ (deriv H) U := hH.deriv hU
  have hH2 : DifferentiableOn ℂ (deriv (deriv H)) U := hH1.deriv hU
  have hmem : ∀ (c : ℂ) (t : ℝ), c = 1 ∨ c = -1 → w + c * (t : ℂ) * I ∈ U := by
    intro c t hc
    rcases hc with rfl | rfl
    · simpa using hline t
    · have := hline (-t); simpa [neg_mul] using this
  set H2 := deriv (deriv H)
  -- The remainder `M` and its first two derivatives.
  let M : ℝ → ℂ := fun h => H (w + 1 * (h : ℂ) * I) + H (w + (-1) * (h : ℂ) * I) - 2 * H w +
    H2 w * (h : ℂ) ^ 2
  let M' : ℝ → ℂ := fun h => deriv H (w + 1 * (h : ℂ) * I) * (1 * I) +
    deriv H (w + (-1) * (h : ℂ) * I) * ((-1) * I) + H2 w * (2 * (h : ℂ))
  let M'' : ℝ → ℂ := fun h => H2 (w + 1 * (h : ℂ) * I) * (1 * I) * (1 * I) +
    H2 (w + (-1) * (h : ℂ) * I) * ((-1) * I) * ((-1) * I) + H2 w * 2
  have hM : ∀ t : ℝ, HasDerivAt M (M' t) t := by
    intro t
    have h1 := hasDerivAt_vertical (H := H) (w := w) (c := 1) (t := t)
      ((hH _ (hmem 1 t (Or.inl rfl))).differentiableAt (hU.mem_nhds (hmem 1 t (Or.inl rfl))))
    have h2 := hasDerivAt_vertical (H := H) (w := w) (c := -1) (t := t)
      ((hH _ (hmem (-1) t (Or.inr rfl))).differentiableAt
        (hU.mem_nhds (hmem (-1) t (Or.inr rfl))))
    exact ((h1.add h2).sub_const (2 * H w)).add ((hasDerivAt_ofReal_sq t).const_mul (H2 w))
  have hM' : ∀ t : ℝ, HasDerivAt M' (M'' t) t := by
    intro t
    have h1 := hasDerivAt_vertical (H := deriv H) (w := w) (c := 1) (t := t)
      ((hH1 _ (hmem 1 t (Or.inl rfl))).differentiableAt (hU.mem_nhds (hmem 1 t (Or.inl rfl))))
    have h2 := hasDerivAt_vertical (H := deriv H) (w := w) (c := -1) (t := t)
      ((hH1 _ (hmem (-1) t (Or.inr rfl))).differentiableAt
        (hU.mem_nhds (hmem (-1) t (Or.inr rfl))))
    have h3 : HasDerivAt (fun r : ℝ => H2 w * (2 * (r : ℂ))) (H2 w * 2) t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 : ℂ)).const_mul (H2 w)
      simpa using this
    exact ((h1.mul_const (1 * I)).add (h2.mul_const ((-1) * I))).add h3
  have hM0 : M 0 = 0 := by simp [M]; ring
  have hM'0 : M' 0 = 0 := by simp [M']
  -- `M''` is small near `0`.
  have hsmall : ∀ ε > 0, ∃ δ > 0, ∀ r : ℝ, |r| ≤ δ → ‖M'' r‖ ≤ ε := by
    intro ε hε
    have hw0 : w ∈ U := by simpa using hline 0
    have hc : ContinuousAt H2 w := ((hH2 w hw0).differentiableAt (hU.mem_nhds hw0)).continuousAt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (by positivity)
    refine ⟨δ / 2, by positivity, fun r hr => ?_⟩
    have hd : ∀ c : ℂ, c = 1 ∨ c = -1 → ‖H2 (w + c * (r : ℂ) * I) - H2 w‖ ≤ ε / 2 := by
      intro c hc'
      have hdist : dist (w + c * (r : ℂ) * I) w < δ := by
        rw [dist_eq_norm, add_sub_cancel_left]
        rcases hc' with rfl | rfl <;>
          simp only [one_mul, neg_mul, norm_neg, norm_mul, Complex.norm_real,
            Complex.norm_I, mul_one, Real.norm_eq_abs] <;> linarith
      have := hδ' hdist
      rw [dist_eq_norm] at this
      exact this.le
    have e : M'' r = -(H2 (w + 1 * (r : ℂ) * I) - H2 w) - (H2 (w + (-1) * (r : ℂ) * I) - H2 w) := by
      simp only [M'']
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [e]
    calc ‖-(H2 (w + 1 * (r : ℂ) * I) - H2 w) - (H2 (w + (-1) * (r : ℂ) * I) - H2 w)‖
        ≤ ‖H2 (w + 1 * (r : ℂ) * I) - H2 w‖ + ‖H2 (w + (-1) * (r : ℂ) * I) - H2 w‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_neg]
      _ ≤ ε / 2 + ε / 2 := add_le_add (hd 1 (Or.inl rfl)) (hd (-1) (Or.inr rfl))
      _ = ε := by ring
  -- Two mean-value steps give `‖M h‖ ≤ ε h²`.
  have hbound : ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, |h| ≤ δ → ‖M h‖ ≤ ε * h ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hsmall ε hε
    refine ⟨δ, hδ, fun h hh => ?_⟩
    have hM'b : ∀ t ∈ Icc (-|h|) |h|, ‖M' t‖ ≤ ε * |h| := by
      intro t ht
      have ht' : |t| ≤ |h| := abs_le.mpr ⟨ht.1, ht.2⟩
      have hmv := (convex_Icc (-|t|) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := M') (f' := M'') (C := ε)
        (fun x _ => (hM' x).hasDerivWithinAt)
        (fun x hx => hδ' x ((abs_le.mpr ⟨hx.1, hx.2⟩).trans (ht'.trans hh)))
        (show (0 : ℝ) ∈ Icc (-|t|) |t| from ⟨by linarith [abs_nonneg t], abs_nonneg t⟩)
        (show t ∈ Icc (-|t|) |t| from ⟨neg_abs_le t, le_abs_self t⟩)
      rw [hM'0, sub_zero, sub_zero, Real.norm_eq_abs] at hmv
      exact hmv.trans (mul_le_mul_of_nonneg_left ht' hε.le)
    have hmv := (convex_Icc (-|h|) |h|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := M) (f' := M') (C := ε * |h|) (fun x _ => (hM x).hasDerivWithinAt) hM'b
      (show (0 : ℝ) ∈ Icc (-|h|) |h| from ⟨by linarith [abs_nonneg h], abs_nonneg h⟩)
      (show h ∈ Icc (-|h|) |h| from ⟨neg_abs_le h, le_abs_self h⟩)
    rw [hM0, sub_zero, sub_zero, Real.norm_eq_abs] at hmv
    calc ‖M h‖ ≤ ε * |h| * |h| := hmv
      _ = ε * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  -- Conclude.
  have hre : ∀ h : ℝ, h ≠ 0 → (2 * (H w).re - (H (w + 1 * (h : ℂ) * I)).re -
      (H (w + (-1) * (h : ℂ) * I)).re) / h ^ 2 = (H2 w).re - (M h).re / h ^ 2 := by
    intro h hh
    have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
    have hMre : (M h).re = (H (w + 1 * (h : ℂ) * I)).re + (H (w + (-1) * (h : ℂ) * I)).re -
        2 * (H w).re + (H2 w).re * h ^ 2 := by
      simp only [M, Complex.add_re, Complex.sub_re, Complex.mul_re]
      have : ((h : ℂ) ^ 2).re = h ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
      have him : ((h : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
      rw [this, him]
      simp
    rw [hMre]
    field_simp
    ring
  have hlim0 : Tendsto (fun h : ℝ => (M h).re / h ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hbound (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun h hh hdist => ?_⟩
    have hh0 : h ≠ 0 := hh
    have hpos : 0 < h ^ 2 := by positivity
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs] at hdist ⊢
    have hb := hδ' h hdist.le
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    calc |(M h).re| ≤ ‖M h‖ := Complex.abs_re_le_norm _
      _ ≤ ε / 2 * h ^ 2 := hb
      _ < ε * h ^ 2 := by nlinarith
  have h := (tendsto_const_nhds (x := (H2 w).re)).sub hlim0
  rw [sub_zero] at h
  exact h.congr' (eventually_nhdsWithin_of_forall fun h hh => (hre h hh).symm)

/-! ## 3. Even derivatives -/

/-- **Second derivatives keep positive-definite vertical sections.** -/
theorem isPosDef_re_deriv_deriv_vertical {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hH : DifferentiableOn ℂ H U) {σ : ℝ} (hline : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I ∈ U)
    (hpd : IsPosDef fun u : ℝ => (H ((σ : ℂ) + (u : ℂ) * I)).re) :
    IsPosDef fun u : ℝ => (deriv (deriv H) ((σ : ℂ) + (u : ℂ) * I)).re := by
  set φ : ℝ → ℝ := fun u => (H ((σ : ℂ) + (u : ℂ) * I)).re with hφ
  refine isPosDef_of_tendsto (l := 𝓝[≠] (0 : ℝ))
    (ψ := fun h u => (1 / h ^ 2) * (2 * φ u - φ (u + h) - φ (u - h))) ?_ ?_
  · exact Eventually.of_forall fun h =>
      isPosDef_const_mul (isPosDef_secondDiff hpd h) (by positivity)
  · intro u
    have hl : ∀ t : ℝ, ((σ : ℂ) + (u : ℂ) * I) + (t : ℂ) * I ∈ U := fun t => by
      have := hline (u + t)
      convert this using 1
      push_cast
      ring
    have h := tendsto_secondDiffQuotient_re hU hH hl
    refine h.congr' (eventually_nhdsWithin_of_forall fun h _ => ?_)
    have e1 : (σ : ℂ) + ((u + h : ℝ) : ℂ) * I = (σ : ℂ) + (u : ℂ) * I + 1 * (h : ℂ) * I := by
      push_cast; ring
    have e2 : (σ : ℂ) + ((u - h : ℝ) : ℂ) * I = (σ : ℂ) + (u : ℂ) * I + (-1) * (h : ℂ) * I := by
      push_cast; ring
    simp only [hφ, e1, e2]
    ring

theorem differentiableOn_iterate_deriv {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : DifferentiableOn ℂ G U) (m : ℕ) : DifferentiableOn ℂ (deriv^[m] G) U := by
  induction m with
  | zero => simpa using hG
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.deriv hU

/-- **Every even derivative has positive-definite vertical sections.** -/
theorem isPosDef_re_iterate_deriv_two_mul {G : ℂ → ℂ} {a : ℝ}
    (hG : DifferentiableOn ℂ G {s : ℂ | a < s.re})
    (hpd : ∀ σ : ℝ, a < σ → IsPosDef fun u : ℝ => (G ((σ : ℂ) + (u : ℂ) * I)).re) (k : ℕ) :
    ∀ σ : ℝ, a < σ → IsPosDef fun u : ℝ => ((deriv^[2 * k] G) ((σ : ℂ) + (u : ℂ) * I)).re := by
  have hU : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  induction k with
  | zero => simpa using hpd
  | succ k ih =>
    intro σ hσ
    have e : deriv^[2 * (k + 1)] G = deriv (deriv (deriv^[2 * k] G)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
    rw [e]
    exact isPosDef_re_deriv_deriv_vertical hU (differentiableOn_iterate_deriv hU hG (2 * k))
      (fun t => by simp [hσ]) (ih σ hσ)

/-- **Even derivatives are nonnegative on the real axis.** -/
theorem re_iterate_deriv_two_mul_nonneg {G : ℂ → ℂ} {a : ℝ}
    (hG : DifferentiableOn ℂ G {s : ℂ | a < s.re})
    (hpd : ∀ σ : ℝ, a < σ → IsPosDef fun u : ℝ => (G ((σ : ℂ) + (u : ℂ) * I)).re) (k : ℕ)
    {σ : ℝ} (hσ : a < σ) : 0 ≤ ((deriv^[2 * k] G) (σ : ℂ)).re := by
  have h := isPosDef_apply_zero_nonneg (isPosDef_re_iterate_deriv_two_mul hG hpd k σ hσ)
  simpa using h

/-! ## 4. Real derivatives on the real axis -/

/-- A holomorphic function real on a real ray has real derivatives there. -/
theorem im_deriv_eq_zero_of_real {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {a : ℝ} (hsub : ∀ x : ℝ, a < x → (x : ℂ) ∈ U)
    (hreal : ∀ x : ℝ, a < x → (f x).im = 0) {x : ℝ} (hx : a < x) : (deriv f x).im = 0 := by
  have hd : HasDerivAt f (deriv f x) (x : ℂ) :=
    ((hf _ (hsub x hx)).differentiableAt (hU.mem_nhds (hsub x hx))).hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => (f y).im) (deriv f x).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => (f y).im) 0 x := by
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy using hreal y hy
  exact h1.unique h2

theorem im_iterate_deriv_eq_zero_of_real {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {a : ℝ} (hsub : ∀ x : ℝ, a < x → (x : ℂ) ∈ U)
    (hreal : ∀ x : ℝ, a < x → (f x).im = 0) (k : ℕ) {x : ℝ} (hx : a < x) :
    ((deriv^[k] f) x).im = 0 := by
  induction k generalizing x with
  | zero => simpa using hreal x hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact im_deriv_eq_zero_of_real hU (differentiableOn_iterate_deriv hU hf k) hsub
      (fun y hy => ih hy) hx

/-- The real tower of a holomorphic function along the real axis. -/
theorem hasDerivAt_re_iterate_deriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (k : ℕ) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    HasDerivAt (fun y : ℝ => ((deriv^[k] f) y).re) ((deriv^[k + 1] f) x).re x := by
  have hd := ((differentiableOn_iterate_deriv hU hf k _ hx).differentiableAt
    (hU.mem_nhds hx)).hasDerivAt
  rw [Function.iterate_succ_apply']
  exact hd.real_of_complex

/-! ## 5. Odd derivatives from convexity and growth -/

private theorem le_sub_of_deriv_ge {g g' : ℝ → ℝ} {a x₁ m : ℝ} (hx₁ : a < x₁)
    (hder : ∀ x, a < x → HasDerivAt g (g' x) x) (hm : ∀ x, x₁ ≤ x → m ≤ g' x) :
    ∀ x, x₁ ≤ x → g x₁ + m * (x - x₁) ≤ g x := by
  intro x hx
  have hcont : ContinuousOn g (Ici x₁) := fun y hy =>
    (hder y (lt_of_lt_of_le hx₁ hy)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior (Ici x₁)) := by
    rw [interior_Ici]
    exact fun y hy => (hder y (lt_trans hx₁ hy)).differentiableAt.differentiableWithinAt
  have h := (convex_Ici x₁).mul_sub_le_image_sub_of_le_deriv hcont hdiff (C := m)
    (fun y hy => by
      rw [interior_Ici] at hy
      rw [(hder y (lt_trans hx₁ hy)).deriv]
      exact hm y hy.le) x₁ self_mem_Ici x hx hx
  linarith

private theorem monotone_of_deriv_nonneg {g g' : ℝ → ℝ} {a : ℝ}
    (hder : ∀ x, a < x → HasDerivAt g (g' x) x) (hnn : ∀ x, a < x → 0 ≤ g' x) {x y : ℝ}
    (hx : a < x) (hxy : x ≤ y) : g x ≤ g y := by
  have h := le_sub_of_deriv_ge (m := 0) hx hder (fun z hz => hnn z (lt_of_lt_of_le hx hz)) y hxy
  linarith

/-- Linear growth beats square-root growth. -/
private theorem exists_lin_gt_sqrt {m : ℝ} (hm : 0 < m) (b C L : ℝ) :
    ∃ X : ℝ, L ≤ X ∧ C * Real.sqrt X < m * X + b := by
  set s : ℝ := max (max 1 L) ((|C| + |b| + 1) / m)
  have hs1 : 1 ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have hsL : L ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  have hsm : (|C| + |b| + 1) / m ≤ s := le_max_right _ _
  have hs0 : 0 ≤ s := by linarith
  refine ⟨s ^ 2, by nlinarith, ?_⟩
  rw [Real.sqrt_sq hs0]
  have h1 : |C| + |b| + 1 ≤ m * s := by rwa [div_le_iff₀ hm, mul_comm] at hsm
  have h2 : (|C| + |b| + 1) * s ≤ m * s ^ 2 := by nlinarith
  nlinarith [le_abs_self C, neg_abs_le b, abs_nonneg b, abs_nonneg C]

/-- **Odd derivatives are nonpositive.** A real tower on `(a, ∞)` whose even members are
nonnegative and whose base grows at most like `√x` has nonpositive odd members: a positive odd
derivative would make the even derivative below it grow linearly. -/
theorem tower_odd_nonpos {T : ℕ → ℝ → ℝ} {a : ℝ}
    (hder : ∀ k x, a < x → HasDerivAt (T k) (T (k + 1) x) x)
    (heven : ∀ j x, a < x → 0 ≤ T (2 * j) x)
    {C x₀ : ℝ} (hgrowth : ∀ x, x₀ ≤ x → T 0 x ≤ C * Real.sqrt x) :
    ∀ j x, a < x → T (2 * j + 1) x ≤ 0 := by
  intro j
  induction j with
  | zero =>
    intro x₁ hx₁
    by_contra hpos
    push Not at hpos
    have hmono : ∀ y, x₁ ≤ y → T 1 x₁ ≤ T 1 y := fun y hy =>
      monotone_of_deriv_nonneg (hder 1) (fun z hz => heven 1 z hz) hx₁ hy
    have hlin := le_sub_of_deriv_ge hx₁ (hder 0) (m := T 1 x₁) (fun y hy => hmono y hy)
    obtain ⟨X, hXL, hX⟩ := exists_lin_gt_sqrt hpos (T 0 x₁ - T 1 x₁ * x₁) C (max x₀ x₁)
    have h1 := hlin X ((le_max_right _ _).trans hXL)
    have h2 := hgrowth X ((le_max_left _ _).trans hXL)
    linarith
  | succ j ih =>
    intro x₁ hx₁
    by_contra hpos
    push Not at hpos
    have e1 : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
    rw [e1] at hpos
    set m := T (2 * j + 3) x₁ with hm
    have hmono : ∀ y, x₁ ≤ y → m ≤ T (2 * j + 3) y := fun y hy =>
      monotone_of_deriv_nonneg (hder (2 * j + 3))
        (fun z hz => by simpa [show 2 * j + 3 + 1 = 2 * (j + 2) by ring] using heven (j + 2) z hz)
        hx₁ hy
    have hlin := le_sub_of_deriv_ge hx₁ (hder (2 * j + 2)) (m := m) hmono
    have hev : 0 ≤ T (2 * j + 2) x₁ := by
      simpa [show 2 * j + 2 = 2 * (j + 1) by ring] using heven (j + 1) x₁ hx₁
    set x₂ := x₁ + 1 / m
    have hx₂ : x₁ ≤ x₂ := by have : 0 < 1 / m := by positivity
                             linarith
    have hge1 : ∀ y, x₂ ≤ y → 1 ≤ T (2 * j + 2) y := by
      intro y hy
      have := hlin y (hx₂.trans hy)
      have hmy : 1 ≤ m * (y - x₁) := by
        have : 1 / m ≤ y - x₁ := by linarith
        rwa [div_le_iff₀ hpos, mul_comm] at this
      linarith
    have hx₂a : a < x₂ := lt_of_lt_of_le hx₁ hx₂
    have hlin2 := le_sub_of_deriv_ge hx₂a (hder (2 * j + 1)) (m := 1) hge1
    set y := x₂ + |T (2 * j + 1) x₂| + 1
    have hy : x₂ ≤ y := by have := abs_nonneg (T (2 * j + 1) x₂); linarith
    have h1 := hlin2 y hy
    have h2 := ih y (lt_of_lt_of_le hx₂a hy)
    have h3 := neg_abs_le (T (2 * j + 1) x₂)
    have : y - x₂ = |T (2 * j + 1) x₂| + 1 := by ring
    nlinarith

/-! ## 6. From the logarithmic derivative to the function -/

theorem differentiableOn_neg_logDeriv {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hF0 : ∀ s ∈ U, F s ≠ 0) :
    DifferentiableOn ℂ (fun s => -logDeriv F s) U := by
  have h := ((hF.deriv hU).div hF fun s hs => hF0 s hs).neg
  refine h.congr fun s _ => ?_
  simp [logDeriv_apply]

/-- **Leibniz for `F' = −G F`.** `F^{(k+1)} = −Σ_i C(k,i) G^{(i)} F^{(k−i)}` on `U`. -/
theorem iterate_deriv_succ_eq {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hF0 : ∀ s ∈ U, F s ≠ 0) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    (deriv^[k + 1] F) z = -∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℂ) * (deriv^[i] (fun s => -logDeriv F s)) z * (deriv^[k - i] F) z := by
  set G : ℂ → ℂ := fun s => -logDeriv F s
  have hGd : DifferentiableOn ℂ G U := differentiableOn_neg_logDeriv hU hF hF0
  have heq : deriv F =ᶠ[𝓝 z] (fun w => -(G w * F w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simp only [G, logDeriv_apply]
    field_simp [hF0 w hw]
  rw [Function.iterate_succ_apply, ← iteratedDeriv_eq_iterate, heq.iteratedDeriv_eq,
    iteratedDeriv_fun_neg,
    iteratedDeriv_fun_mul ((hGd.contDiffOn hU).contDiffAt (hU.mem_nhds hz))
      ((hF.contDiffOn hU).contDiffAt (hU.mem_nhds hz))]
  simp only [iteratedDeriv_eq_iterate]

/-- **Complete monotonicity transfers from `−F'/F` to `F`.** If `F` is holomorphic, nonvanishing,
real and positive on `(a, ∞)` and `(−1)^k (−F'/F)^{(k)} ≥ 0` there, then `(−1)^k F^{(k)} ≥ 0`
there: each derivative of `F` is a positive combination of products of the two towers. -/
theorem alternating_iterate_deriv_nonneg {F : ℂ → ℂ} {a : ℝ}
    (hF : DifferentiableOn ℂ F {s : ℂ | a < s.re}) (hF0 : ∀ s : ℂ, a < s.re → F s ≠ 0)
    (hreal : ∀ x : ℝ, a < x → (F x).im = 0) (hpos : ∀ x : ℝ, a < x → 0 < (F x).re)
    (hG : ∀ (k : ℕ) (x : ℝ), a < x →
      0 ≤ (-1) ^ k * ((deriv^[k] (fun s => -logDeriv F s)) x).re) :
    ∀ (k : ℕ) (x : ℝ), a < x → 0 ≤ (-1) ^ k * ((deriv^[k] F) x).re := by
  set U : Set ℂ := {s : ℂ | a < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set G : ℂ → ℂ := fun s => -logDeriv F s
  have hGd : DifferentiableOn ℂ G U := differentiableOn_neg_logDeriv hU hF fun s hs => hF0 s hs
  have hsub : ∀ x : ℝ, a < x → (x : ℂ) ∈ U := fun x hx => by simpa [U] using hx
  have hFr := im_iterate_deriv_eq_zero_of_real hU hF hsub hreal
  have hGreal : ∀ x : ℝ, a < x → (G x).im = 0 := by
    intro x hx
    have h1 := hFr 1 hx
    simp only [Function.iterate_one] at h1
    simp only [G, logDeriv_apply, Complex.neg_im, Complex.div_im, h1, hreal x hx]
    ring
  have hGr := im_iterate_deriv_eq_zero_of_real hU hGd hsub hGreal
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    rcases k with _ | k
    · simpa using (hpos x hx).le
    · rw [iterate_deriv_succ_eq hU hF (fun s hs => hF0 s hs) k (hsub x hx), Complex.neg_re,
        Complex.re_sum]
      have hterm : ∀ i ∈ Finset.range (k + 1),
          ((k.choose i : ℂ) * (deriv^[i] G) x * (deriv^[k - i] F) x).re =
            (k.choose i : ℝ) * ((deriv^[i] G) x).re * ((deriv^[k - i] F) x).re := by
        intro i _
        rw [Complex.mul_re, Complex.mul_re, hGr i hx, hFr (k - i) hx]
        simp
      rw [Finset.sum_congr rfl hterm, mul_neg, ← neg_mul, Finset.mul_sum]
      refine Finset.sum_nonneg fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsign : -(-1 : ℝ) ^ (k + 1) = (-1) ^ i * (-1) ^ (k - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hik, pow_succ]
        ring
      have h1 := hG i x hx
      have h2 := ih (k - i) (by omega) x hx
      have hc : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
      calc (0 : ℝ) ≤ (k.choose i : ℝ) * (((-1) ^ i * ((deriv^[i] G) x).re) *
            ((-1) ^ (k - i) * ((deriv^[k - i] F) x).re)) :=
            mul_nonneg hc (mul_nonneg h1 h2)
        _ = -(-1 : ℝ) ^ (k + 1) * ((k.choose i : ℝ) * ((deriv^[i] G) x).re *
            ((deriv^[k - i] F) x).re) := by rw [hsign]; ring

end GaloisForLFunctions.StripBochnerWeilForcing
