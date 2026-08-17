import GaloisForLFunctions.HTGeometry.CosineCapProfile

/-!
# Domination of a cosine arc by a positive exponential sum

A positive exponential sum `R(t) = ∑ c_i e^{a_i t}` is compared with the modulated cosine
`2 e^{β t} cos (γ (t - p))` on the arc `|t - p| ≤ π/(2γ)` where the cosine is nonnegative.  The
comparison is **not** a sign-change count: the difference is not an exponential sum with real
exponents, and its zero set can be infinite.

What replaces the count is a separation.  `log R(t) - β t` is convex, the cap
`log 2 + log cos (γ (t - p))` is concave, and a convex function dominates a concave one on an
interval exactly when a single line separates them.  Exponentiating, exactly when a **single
exponential** `e^{L + (β+ν) t}` separates them.  The condition on that exponential is closed form:
its logarithm at the centre of the arc must reach the Legendre profile `Φ(ν/γ)` of the cap.

`R(t) ≥ 2 e^{β t} cos (γ (t - p))` on the arc
  ⟺ `∃ ν L,  e^{L + (β+ν) t} ≤ R(t)` for **all** `t`, and `Φ(ν/γ) ≤ L + ν p`.

The separating exponential is produced at the point of the arc where `2 cos(γ(t-p)) e^{βt}/R(t)` is
largest; there the tangency forces `γ (t - p) = -arctan (ν/γ)`, which is precisely the point at
which the cap attains its Legendre profile.
-/

open Set Real Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {m : ℕ}

/-- The comparison ratio whose maximum over the arc locates the separating exponential. -/
noncomputable def arcRatio (c a : Fin m → ℝ) (β γ p : ℝ) (t : ℝ) : ℝ :=
  2 * Real.cos (γ * (t - p)) * Real.exp (β * t) / expSum c a t

/-! ## Derivatives -/

theorem hasDerivAt_log_expSum (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i) (t : ℝ) :
    HasDerivAt (fun s => Real.log (expSum c a s))
      (expSum (fun i => c i * a i) a t / expSum c a t) t :=
  (hasDerivAt_expSum c a t).log (ne_of_gt (expSum_pos c a hm hc t))

theorem hasDerivAt_log_cos_arc {γ p t : ℝ} (h : Real.cos (γ * (t - p)) ≠ 0) :
    HasDerivAt (fun s => Real.log (Real.cos (γ * (s - p)))) (-γ * Real.tan (γ * (t - p))) t := by
  have hin : HasDerivAt (fun s : ℝ => γ * (s - p)) γ t := by
    simpa using ((hasDerivAt_id t).sub_const p).const_mul γ
  have hcos : HasDerivAt (fun s : ℝ => Real.cos (γ * (s - p)))
      (-Real.sin (γ * (t - p)) * γ) t := hin.cos
  refine (hcos.log h).congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-! ## The criterion -/

/-- **Sufficiency.**  A single exponential reaching the Legendre profile of the cap at the centre of
the arc dominates the modulated cosine on the whole arc. -/
theorem cos_arc_le_of_separating (c a : Fin m → ℝ) {β γ p ν L : ℝ} (hγ : 0 < γ)
    (hsep : ∀ t : ℝ, Real.exp (L + (β + ν) * t) ≤ expSum c a t)
    (hprof : capProfile (ν / γ) ≤ L + ν * p) :
    ∀ t ∈ Icc (p - π / (2 * γ)) (p + π / (2 * γ)),
      2 * Real.exp (β * t) * Real.cos (γ * (t - p)) ≤ expSum c a t := by
  intro t ht
  have humem : γ * (t - p) ∈ Icc (-(π / 2)) (π / 2) := by
    constructor
    · have h1 : p - π / (2 * γ) ≤ t := ht.1
      have : -(π / (2 * γ)) ≤ t - p := by linarith
      have h2 := mul_le_mul_of_nonneg_left this hγ.le
      calc -(π / 2) = γ * -(π / (2 * γ)) := by field_simp
        _ ≤ γ * (t - p) := h2
    · have h1 : t ≤ p + π / (2 * γ) := ht.2
      have : t - p ≤ π / (2 * γ) := by linarith
      have h2 := mul_le_mul_of_nonneg_left this hγ.le
      calc γ * (t - p) ≤ γ * (π / (2 * γ)) := h2
        _ = π / 2 := by field_simp
  have hcap := two_mul_cos_le_exp_capProfile (ν / γ) humem
  have hexp : Real.exp (β * t) * (2 * Real.cos (γ * (t - p)))
      ≤ Real.exp (β * t) * Real.exp (capProfile (ν / γ) + ν / γ * (γ * (t - p))) :=
    mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le
  have hrw : Real.exp (β * t) * Real.exp (capProfile (ν / γ) + ν / γ * (γ * (t - p)))
      = Real.exp (β * t + capProfile (ν / γ) + ν * (t - p)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hle : β * t + capProfile (ν / γ) + ν * (t - p) ≤ L + (β + ν) * t := by
    have := hprof
    nlinarith [this]
  calc 2 * Real.exp (β * t) * Real.cos (γ * (t - p))
      = Real.exp (β * t) * (2 * Real.cos (γ * (t - p))) := by ring
    _ ≤ Real.exp (β * t) * Real.exp (capProfile (ν / γ) + ν / γ * (γ * (t - p))) := hexp
    _ = Real.exp (β * t + capProfile (ν / γ) + ν * (t - p)) := hrw
    _ ≤ Real.exp (L + (β + ν) * t) := Real.exp_le_exp.mpr hle
    _ ≤ expSum c a t := hsep t


/-! ## Necessity: the separating exponential exists -/

private theorem arc_mem_Ioo {γ p t : ℝ} (hγ : 0 < γ)
    (ht : t ∈ Ioo (p - π / (2 * γ)) (p + π / (2 * γ))) :
    γ * (t - p) ∈ Ioo (-(π / 2)) (π / 2) := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  constructor
  · have h1 : -(π / (2 * γ)) < t - p := by linarith [ht.1]
    have h2 := mul_lt_mul_of_pos_left h1 hγ
    calc -(π / 2) = γ * -(π / (2 * γ)) := by field_simp
      _ < γ * (t - p) := h2
  · have h1 : t - p < π / (2 * γ) := by linarith [ht.2]
    have h2 := mul_lt_mul_of_pos_left h1 hγ
    calc γ * (t - p) < γ * (π / (2 * γ)) := h2
      _ = π / 2 := by field_simp

private theorem arcRatio_pos (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    (β γ p : ℝ) {t : ℝ} (ht : 0 < Real.cos (γ * (t - p))) : 0 < arcRatio c a β γ p t := by
  have hR : 0 < expSum c a t := expSum_pos c a hm hc t
  rw [arcRatio]
  exact div_pos (mul_pos (by linarith) (Real.exp_pos _)) hR

private theorem log_arcRatio (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    (β γ p : ℝ) {t : ℝ} (ht : 0 < Real.cos (γ * (t - p))) :
    Real.log (arcRatio c a β γ p t)
      = Real.log 2 + Real.log (Real.cos (γ * (t - p))) + β * t - Real.log (expSum c a t) := by
  have hR : 0 < expSum c a t := expSum_pos c a hm hc t
  rw [arcRatio, Real.log_div (by positivity) (ne_of_gt hR),
    Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
    Real.log_mul (by norm_num) (ne_of_gt ht), Real.log_exp]

/-- **Necessity.**  If a positive exponential sum dominates the modulated cosine on the whole arc,
then a single exponential separates them: one that lies below `R` everywhere and whose logarithm
reaches the Legendre profile of the cap at the centre of the arc.

The separating exponent is the logarithmic derivative of `R` at the point where the ratio
`2 cos(γ(t-p)) e^{βt} / R(t)` is largest; the tangency there pins `γ(t-p) = -arctan(ν/γ)`, the exact
point at which the cap attains its profile. -/
theorem exists_separating_of_cos_arc_le (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    {β γ p : ℝ} (hγ : 0 < γ)
    (h : ∀ t ∈ Icc (p - π / (2 * γ)) (p + π / (2 * γ)),
      2 * Real.exp (β * t) * Real.cos (γ * (t - p)) ≤ expSum c a t) :
    ∃ ν L : ℝ, (∀ t : ℝ, Real.exp (L + (β + ν) * t) ≤ expSum c a t)
      ∧ capProfile (ν / γ) ≤ L + ν * p := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hw : 0 < π / (2 * γ) := by positivity
  -- the ratio attains its maximum on the closed arc
  have hcont : Continuous (arcRatio c a β γ p) := by
    refine Continuous.div (by fun_prop) ((contDiff_expSum c a).continuous) ?_
    exact fun t => ne_of_gt (expSum_pos c a hm hc t)
  have hpK : p ∈ Icc (p - π / (2 * γ)) (p + π / (2 * γ)) := ⟨by linarith, by linarith⟩
  obtain ⟨ts, htsK, htsmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨p, hpK⟩ hcont.continuousOn
  -- the maximum is positive, so it is not attained at an endpoint
  have hpratio : 0 < arcRatio c a β γ p p := by
    refine arcRatio_pos c a hm hc β γ p ?_
    simp
  have htspos : 0 < arcRatio c a β γ p ts := lt_of_lt_of_le hpratio (htsmax hpK)
  have hendR : arcRatio c a β γ p (p + π / (2 * γ)) = 0 := by
    have : γ * (p + π / (2 * γ) - p) = π / 2 := by field_simp; ring
    rw [arcRatio, this, Real.cos_pi_div_two]
    ring
  have hendL : arcRatio c a β γ p (p - π / (2 * γ)) = 0 := by
    have : γ * (p - π / (2 * γ) - p) = -(π / 2) := by field_simp; ring
    rw [arcRatio, this, Real.cos_neg, Real.cos_pi_div_two]
    ring
  have htsIoo : ts ∈ Ioo (p - π / (2 * γ)) (p + π / (2 * γ)) := by
    refine ⟨lt_of_le_of_ne htsK.1 (fun hcon => ?_), lt_of_le_of_ne htsK.2 (fun hcon => ?_)⟩
    · rw [← hcon, hendL] at htspos; exact lt_irrefl 0 htspos
    · rw [hcon, hendR] at htspos; exact lt_irrefl 0 htspos
  have humem : γ * (ts - p) ∈ Ioo (-(π / 2)) (π / 2) := arc_mem_Ioo hγ htsIoo
  have hcosu : 0 < Real.cos (γ * (ts - p)) := Real.cos_pos_of_mem_Ioo humem
  have hRts : 0 < expSum c a ts := expSum_pos c a hm hc ts
  -- the tangency condition at the maximiser
  set ν : ℝ := expSum (fun i => c i * a i) a ts / expSum c a ts - β with hν
  set D : ℝ → ℝ := fun t =>
    Real.log (expSum c a t) - β * t - Real.log 2 - Real.log (Real.cos (γ * (t - p))) with hD
  have hlocmin : IsLocalMin D ts := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds htsIoo) ?_
    intro t ht
    have hcost : 0 < Real.cos (γ * (t - p)) := Real.cos_pos_of_mem_Ioo (arc_mem_Ioo hγ ht)
    have hle : arcRatio c a β γ p t ≤ arcRatio c a β γ p ts :=
      htsmax (Ioo_subset_Icc_self ht)
    have hlog := Real.log_le_log (arcRatio_pos c a hm hc β γ p hcost) hle
    rw [log_arcRatio c a hm hc β γ p hcost, log_arcRatio c a hm hc β γ p hcosu] at hlog
    simp only [hD]
    linarith
  have hDderiv : HasDerivAt D (ν + γ * Real.tan (γ * (ts - p))) ts := by
    have h1 : HasDerivAt (fun t => Real.log (expSum c a t))
        (expSum (fun i => c i * a i) a ts / expSum c a ts) ts :=
      hasDerivAt_log_expSum c a hm hc ts
    have h2 : HasDerivAt (fun t : ℝ => β * t) β ts := by
      simpa using (hasDerivAt_id ts).const_mul β
    have h3 : HasDerivAt (fun _ : ℝ => Real.log 2) 0 ts := hasDerivAt_const ts _
    have h4 : HasDerivAt (fun t => Real.log (Real.cos (γ * (t - p))))
        (-γ * Real.tan (γ * (ts - p))) ts := hasDerivAt_log_cos_arc (ne_of_gt hcosu)
    refine (((h1.sub h2).sub h3).sub h4).congr_deriv ?_
    rw [hν]
    ring
  have hzero : ν + γ * Real.tan (γ * (ts - p)) = 0 := hlocmin.hasDerivAt_eq_zero hDderiv
  have htan : Real.tan (γ * (ts - p)) = -(ν / γ) := by
    field_simp
    linarith
  have hueq : γ * (ts - p) = -Real.arctan (ν / γ) := by
    have := Real.arctan_tan humem.1 humem.2
    rw [htan, Real.arctan_neg] at this
    linarith
  refine ⟨ν, Real.log (expSum c a ts) - (β + ν) * ts, ?_, ?_⟩
  · intro t
    have hsup := exp_supporting_le_expSum c a hm hc ts t
    have hcoef : expSum (fun i => c i * a i) a ts / expSum c a ts = β + ν := by
      rw [hν]; ring
    rw [hcoef] at hsup
    have hrw : Real.log (expSum c a ts) - (β + ν) * ts + (β + ν) * t
        = Real.log (expSum c a ts) + (β + ν) * (t - ts) := by ring
    rw [hrw]
    exact hsup
  · -- the cap value at the tangency point
    have hcap : capProfile (ν / γ)
        = Real.log 2 + Real.log (Real.cos (γ * (ts - p))) - ν * (ts - p) := by
      have hkey := log_cos_sub_eq_capProfile (ν / γ)
      rw [← hueq] at hkey
      rw [← hkey]
      field_simp
    -- the hypothesis at the tangency point
    have hts := h ts htsK
    have hlog : Real.log 2 + β * ts + Real.log (Real.cos (γ * (ts - p)))
        ≤ Real.log (expSum c a ts) := by
      have hpos : (0 : ℝ) < 2 * Real.exp (β * ts) * Real.cos (γ * (ts - p)) := by
        exact mul_pos (by positivity) hcosu
      have := Real.log_le_log hpos hts
      rw [Real.log_mul (by positivity) (ne_of_gt hcosu),
        Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at this
      linarith
    rw [hcap]
    linarith

/-- **The arc criterion.**  A positive exponential sum dominates the modulated cosine on the arc
where the cosine is nonnegative exactly when a single exponential separates the two, and the
separating exponential is constrained only by the Legendre profile of the cap at the arc centre. -/
theorem cos_arc_le_iff_exists_separating (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    {β γ p : ℝ} (hγ : 0 < γ) :
    (∀ t ∈ Icc (p - π / (2 * γ)) (p + π / (2 * γ)),
        2 * Real.exp (β * t) * Real.cos (γ * (t - p)) ≤ expSum c a t)
      ↔ ∃ ν L : ℝ, (∀ t : ℝ, Real.exp (L + (β + ν) * t) ≤ expSum c a t)
          ∧ capProfile (ν / γ) ≤ L + ν * p := by
  constructor
  · exact exists_separating_of_cos_arc_le c a hm hc hγ
  · rintro ⟨ν, L, hsep, hprof⟩
    exact cos_arc_le_of_separating c a hγ hsep hprof

end GaloisForLFunctions.HTGeometry
