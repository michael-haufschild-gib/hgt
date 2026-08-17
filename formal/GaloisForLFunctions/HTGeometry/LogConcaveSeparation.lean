import GaloisForLFunctions.HTGeometry.ExponentialCertificateGap

/-!
# The exact scope of the exponential-profile method

A single exponential separates a positive exponential sum `R` from a comparison function `C` on a
window exactly when `C` is log-concave there, in the tangential form used below: `C` lies under the
exponential tangent to `log C` at every interior point where `C` is positive.  On such a window the
separation is *complete* — domination is equivalent to the existence of the separating exponential —
and the window may be any "hump" of `C`, an interval whose endpoints carry `C ≤ 0`.

This isolates the reason the cosine cap of one conjugate pair is certified exactly while two pairs
are not: one cap is log-concave on its own arc, a sum of two caps is not, and the chord obstruction
of `ExponentialCertificateGap` shows no repair is possible.  What survives is a **finite family of
profiles**, one per hump: `C ≤ R` on the line is equivalent to a separating exponential on each hump
of `C`.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

/-- `C` lies below the exponential tangent to `log C` at every point of `W` where it is positive.
For positive `C` this is exactly concavity of `log C`; the formulation extends across the zeros of
`C` without referring to `log C` there. -/
def LogTangentDominated (C : ℝ → ℝ) (W : Set ℝ) : Prop :=
  ∀ t₀ ∈ W, 0 < C t₀ → ∀ t ∈ W, C t ≤ C t₀ * Real.exp (deriv C t₀ / C t₀ * (t - t₀))

/-! ## The separation theorem on a hump -/

/-- **Completeness of the profile method on a hump.**  If `C` is log-tangent-dominated on a window
whose endpoints carry `C ≤ 0`, and `C` is somewhere positive inside, then domination of `C` by a
positive exponential sum on that window is witnessed by a single exponential lying under the sum on
all of `ℝ`. -/
theorem exists_separating_of_le_on_hump {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    {C : ℝ → ℝ} {u v : ℝ} (huv : u < v)
    (hCcont : Continuous C) (hCdiff : ∀ t, DifferentiableAt ℝ C t)
    (hCu : C u ≤ 0) (hCv : C v ≤ 0) (hw : ∃ w ∈ Ioo u v, 0 < C w)
    (hlt : LogTangentDominated C (Icc u v))
    (hdom : ∀ t ∈ Icc u v, C t ≤ expSum c a t) :
    ∃ ν L : ℝ, (∀ t : ℝ, Real.exp (L + ν * t) ≤ expSum c a t)
      ∧ ∀ t ∈ Icc u v, C t ≤ Real.exp (L + ν * t) := by
  have hRpos : ∀ t : ℝ, 0 < expSum c a t := fun t => expSum_pos c a hm hc t
  set P : ℝ → ℝ := fun t => C t / expSum c a t with hP
  have hPcont : Continuous P :=
    hCcont.div ((contDiff_expSum c a).continuous) (fun t => ne_of_gt (hRpos t))
  obtain ⟨ts, htsK, htsmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨u, left_mem_Icc.mpr huv.le⟩ hPcont.continuousOn
  obtain ⟨w, hwmem, hwpos⟩ := hw
  have hPw : 0 < P w := div_pos hwpos (hRpos w)
  have hPts : 0 < P ts := lt_of_lt_of_le hPw (htsmax (Ioo_subset_Icc_self hwmem))
  have hCts : 0 < C ts := by
    by_contra hcon
    push Not at hcon
    have : P ts ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcon (hRpos ts).le
    linarith
  have htsIoo : ts ∈ Ioo u v := by
    refine ⟨lt_of_le_of_ne htsK.1 (fun hcon => ?_), lt_of_le_of_ne htsK.2 (fun hcon => ?_)⟩
    · rw [← hcon] at hCts; linarith
    · rw [hcon] at hCts; linarith
  -- the ratio has an interior maximum, so the logarithmic derivatives agree there
  set nu : ℝ := expSum (fun i => c i * a i) a ts / expSum c a ts with hnu
  set D : ℝ → ℝ := fun t => Real.log (C t) - Real.log (expSum c a t) with hD
  have hopen : IsOpen ({t : ℝ | 0 < C t} ∩ Ioo u v) :=
    (isOpen_lt continuous_const hCcont).inter isOpen_Ioo
  have hlocmin : IsLocalMax D ts := by
    refine Filter.eventually_of_mem (hopen.mem_nhds ⟨hCts, htsIoo⟩) ?_
    rintro t ⟨hCt, htIoo⟩
    have hle : P t ≤ P ts := htsmax (Ioo_subset_Icc_self htIoo)
    have hlog := Real.log_le_log (div_pos hCt (hRpos t)) hle
    rw [hP] at hlog
    simp only [hD]
    rw [Real.log_div (ne_of_gt hCt) (ne_of_gt (hRpos t)),
      Real.log_div (ne_of_gt hCts) (ne_of_gt (hRpos ts))] at hlog
    linarith
  have hDderiv : HasDerivAt D (deriv C ts / C ts - nu) ts := by
    have h1 : HasDerivAt (fun t => Real.log (C t)) (deriv C ts / C ts) ts :=
      ((hCdiff ts).hasDerivAt).log (ne_of_gt hCts)
    have h2 : HasDerivAt (fun t => Real.log (expSum c a t)) nu ts :=
      hasDerivAt_log_expSum c a hm hc ts
    exact h1.sub h2
  have hzero : deriv C ts / C ts - nu = 0 := hlocmin.hasDerivAt_eq_zero hDderiv
  have hslope : deriv C ts / C ts = nu := by linarith
  refine ⟨nu, Real.log (expSum c a ts) - nu * ts, ?_, ?_⟩
  · intro t
    have hsup := exp_supporting_le_expSum c a hm hc ts t
    rw [← hnu] at hsup
    have hrw : Real.log (expSum c a ts) - nu * ts + nu * t
        = Real.log (expSum c a ts) + nu * (t - ts) := by ring
    rw [hrw]
    exact hsup
  · intro t ht
    have htan := hlt ts (Ioo_subset_Icc_self htsIoo) hCts t ht
    rw [hslope] at htan
    have hCle : C ts ≤ expSum c a ts := hdom ts (Ioo_subset_Icc_self htsIoo)
    have hstep : C ts * Real.exp (nu * (t - ts))
        ≤ expSum c a ts * Real.exp (nu * (t - ts)) :=
      mul_le_mul_of_nonneg_right hCle (Real.exp_pos _).le
    have hrw : Real.exp (Real.log (expSum c a ts) - nu * ts + nu * t)
        = expSum c a ts * Real.exp (nu * (t - ts)) := by
      rw [show Real.log (expSum c a ts) - nu * ts + nu * t
          = Real.log (expSum c a ts) + nu * (t - ts) from by ring, Real.exp_add,
        Real.exp_log (hRpos ts)]
    rw [hrw]
    linarith

/-- The converse is immediate: a separating exponential certifies domination. -/
theorem le_of_separating {m : ℕ} (c a : Fin m → ℝ) {C : ℝ → ℝ} {W : Set ℝ} {ν L : ℝ}
    (hsep : ∀ t : ℝ, Real.exp (L + ν * t) ≤ expSum c a t)
    (hcap : ∀ t ∈ W, C t ≤ Real.exp (L + ν * t)) :
    ∀ t ∈ W, C t ≤ expSum c a t := fun t ht => le_trans (hcap t ht) (hsep t)

/-! ## The piecewise profile criterion -/

/-- **A finite family of profiles replaces the joint profile.**  If the positivity set of `C` is
covered by finitely many humps, each log-tangent-dominated, then `C ≤ R` on the whole line is
equivalent to the existence of one separating exponential per hump. -/
theorem le_iff_forall_separating {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    {C : ℝ → ℝ} (hCcont : Continuous C) (hCdiff : ∀ t, DifferentiableAt ℝ C t)
    {n : ℕ} (u v : Fin n → ℝ) (huv : ∀ k, u k < v k)
    (hCu : ∀ k, C (u k) ≤ 0) (hCv : ∀ k, C (v k) ≤ 0)
    (hw : ∀ k, ∃ w ∈ Ioo (u k) (v k), 0 < C w)
    (hlt : ∀ k, LogTangentDominated C (Icc (u k) (v k)))
    (hcover : ∀ t : ℝ, 0 < C t → ∃ k, t ∈ Icc (u k) (v k)) :
    (∀ t : ℝ, C t ≤ expSum c a t)
      ↔ ∀ k, ∃ ν L : ℝ, (∀ t : ℝ, Real.exp (L + ν * t) ≤ expSum c a t)
          ∧ ∀ t ∈ Icc (u k) (v k), C t ≤ Real.exp (L + ν * t) := by
  constructor
  · intro h k
    exact exists_separating_of_le_on_hump c a hm hc (huv k) hCcont hCdiff (hCu k) (hCv k)
      (hw k) (hlt k) (fun t _ => h t)
  · intro h t
    by_cases hCt : 0 < C t
    · obtain ⟨k, hk⟩ := hcover t hCt
      obtain ⟨ν, L, hsep, hcap⟩ := h k
      exact le_of_separating c a hsep hcap t hk
    · push Not at hCt
      exact le_trans hCt (expSum_pos c a hm hc t).le

/-! ## The cosine cap is log-tangent-dominated -/

theorem log_cos_tangent {u₀ u : ℝ} (h0 : u₀ ∈ Ioo (-(π / 2)) (π / 2))
    (h : u ∈ Ioo (-(π / 2)) (π / 2)) :
    Real.cos u ≤ Real.cos u₀ * Real.exp (-Real.tan u₀ * (u - u₀)) := by
  have hc0 : 0 < Real.cos u₀ := Real.cos_pos_of_mem_Ioo h0
  have hcu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo h
  have hfix : -Real.arctan (-Real.tan u₀) = u₀ := by
    rw [Real.arctan_neg, neg_neg, Real.arctan_tan h0.1 h0.2]
  have hx := capFn_min (-Real.tan u₀) h
  rw [hfix] at hx
  have hlog : Real.log (Real.cos u) ≤ Real.log (Real.cos u₀) + -Real.tan u₀ * (u - u₀) := by
    nlinarith [hx]
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hcu, Real.exp_add, Real.exp_log hc0] at this

theorem arc_mem_Icc {γ p t : ℝ} (hγ : 0 < γ) (ht : t ∈ Icc (p - π / (2 * γ)) (p + π / (2 * γ))) :
    γ * (t - p) ∈ Icc (-(π / 2)) (π / 2) := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  constructor
  · have h1 : -(π / (2 * γ)) ≤ t - p := by linarith [ht.1]
    have h2 := mul_le_mul_of_nonneg_left h1 hγ.le
    calc -(π / 2) = γ * -(π / (2 * γ)) := by field_simp
      _ ≤ γ * (t - p) := h2
  · have h1 : t - p ≤ π / (2 * γ) := by linarith [ht.2]
    have h2 := mul_le_mul_of_nonneg_left h1 hγ.le
    calc γ * (t - p) ≤ γ * (π / (2 * γ)) := h2
      _ = π / 2 := by field_simp

/-- **One cap is log-tangent-dominated on its arc.**  So the profile method of
`ComplexPairArcCriterion` is the case `n = 1` of the piecewise criterion. -/
theorem logTangentDominated_cap (β γ p : ℝ) (hγ : 0 < γ) :
    LogTangentDominated (fun t => 2 * Real.exp (β * t) * Real.cos (γ * (t - p)))
      (Icc (p - π / (2 * γ)) (p + π / (2 * γ))) := by
  intro t₀ ht₀ hpos t ht
  set C : ℝ → ℝ := fun s => 2 * Real.exp (β * s) * Real.cos (γ * (s - p)) with hC
  have hu₀Icc : γ * (t₀ - p) ∈ Icc (-(π / 2)) (π / 2) := arc_mem_Icc hγ ht₀
  have hcos₀ : 0 < Real.cos (γ * (t₀ - p)) := by
    by_contra hcon
    push Not at hcon
    have : C t₀ ≤ 0 := by
      rw [hC]
      have : (0 : ℝ) < 2 * Real.exp (β * t₀) := by positivity
      nlinarith
    linarith
  have hu₀ : γ * (t₀ - p) ∈ Ioo (-(π / 2)) (π / 2) := by
    refine ⟨lt_of_le_of_ne hu₀Icc.1 (fun hcon => ?_), lt_of_le_of_ne hu₀Icc.2 (fun hcon => ?_)⟩
    · rw [← hcon] at hcos₀; simp at hcos₀
    · rw [hcon] at hcos₀; simp at hcos₀
  -- the logarithmic derivative of the cap
  have hderiv : HasDerivAt C
      (C t₀ * (β - γ * Real.tan (γ * (t₀ - p)))) t₀ := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * Real.exp (β * s)) (2 * (β * Real.exp (β * t₀))) t₀ := by
      have hb : HasDerivAt (fun s : ℝ => β * s) β t₀ := by
        simpa using (hasDerivAt_id t₀).const_mul β
      have := (hb.exp).const_mul (2 : ℝ)
      refine this.congr_deriv ?_
      ring
    have hin : HasDerivAt (fun s : ℝ => γ * (s - p)) γ t₀ := by
      simpa using ((hasDerivAt_id t₀).sub_const p).const_mul γ
    have h2 : HasDerivAt (fun s : ℝ => Real.cos (γ * (s - p)))
        (-Real.sin (γ * (t₀ - p)) * γ) t₀ := hin.cos
    refine (h1.mul h2).congr_deriv ?_
    rw [hC, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hslope : deriv C t₀ / C t₀ = β - γ * Real.tan (γ * (t₀ - p)) := by
    rw [hderiv.deriv]
    field_simp
  rw [hslope]
  -- compare the cap at `t` with the tangent exponential
  have huIcc : γ * (t - p) ∈ Icc (-(π / 2)) (π / 2) := arc_mem_Icc hγ ht
  have hpos2 : (0 : ℝ) < C t₀ * Real.exp ((β - γ * Real.tan (γ * (t₀ - p))) * (t - t₀)) :=
    mul_pos hpos (Real.exp_pos _)
  rcases le_total (Real.cos (γ * (t - p))) 0 with hle | hge
  · have : C t ≤ 0 := by
      rw [hC]
      have h2 : (0 : ℝ) < 2 * Real.exp (β * t) := by positivity
      nlinarith
    linarith
  · rcases eq_or_lt_of_le hge with heq | hlt
    · have : C t ≤ 0 := by
        rw [hC]
        have h2 : (0 : ℝ) < 2 * Real.exp (β * t) := by positivity
        nlinarith [heq]
      linarith
    have hu : γ * (t - p) ∈ Ioo (-(π / 2)) (π / 2) := by
      refine ⟨lt_of_le_of_ne huIcc.1 (fun hcon => ?_), lt_of_le_of_ne huIcc.2 (fun hcon => ?_)⟩
      · rw [← hcon] at hlt; simp at hlt
      · rw [hcon] at hlt; simp at hlt
    have hcap := log_cos_tangent hu₀ hu
    have harg : γ * (t - p) - γ * (t₀ - p) = γ * (t - t₀) := by ring
    rw [harg] at hcap
    have hexp : C t₀ * Real.exp ((β - γ * Real.tan (γ * (t₀ - p))) * (t - t₀))
        = 2 * Real.exp (β * t) * (Real.cos (γ * (t₀ - p))
            * Real.exp (-Real.tan (γ * (t₀ - p)) * (γ * (t - t₀)))) := by
      rw [hC]
      rw [show (2 : ℝ) * Real.exp (β * t₀) * Real.cos (γ * (t₀ - p))
            * Real.exp ((β - γ * Real.tan (γ * (t₀ - p))) * (t - t₀))
          = 2 * (Real.exp (β * t₀) * Real.exp ((β - γ * Real.tan (γ * (t₀ - p))) * (t - t₀)))
            * Real.cos (γ * (t₀ - p)) from by ring, ← Real.exp_add]
      rw [show (2 : ℝ) * Real.exp (β * t) * (Real.cos (γ * (t₀ - p))
            * Real.exp (-Real.tan (γ * (t₀ - p)) * (γ * (t - t₀))))
          = 2 * (Real.exp (β * t) * Real.exp (-Real.tan (γ * (t₀ - p)) * (γ * (t - t₀))))
            * Real.cos (γ * (t₀ - p)) from by ring, ← Real.exp_add]
      congr 3
      ring
    rw [hexp, hC]
    have hmul : Real.cos (γ * (t - p))
        ≤ Real.cos (γ * (t₀ - p)) * Real.exp (-Real.tan (γ * (t₀ - p)) * (γ * (t - t₀))) := hcap
    have h2 : (0 : ℝ) ≤ 2 * Real.exp (β * t) := by positivity
    exact mul_le_mul_of_nonneg_left hmul h2

end GaloisForLFunctions.HTGeometry
