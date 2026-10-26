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

end GaloisForLFunctions.StripBochnerWeilForcing
