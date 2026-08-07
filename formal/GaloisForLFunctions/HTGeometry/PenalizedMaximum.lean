import Mathlib

/-!
# Penalized maxima

Adding a linear penalty `−δ|L − L₀|` to a bounded continuous profile forces a maximum to exist: the
penalty drives the sum to `−∞`, so the supremum is attained on a compact set.  At such a maximizer
the profile obeys a one-sided Lipschitz inequality with constant the penalty slope,

`H(X + s) ≤ H(X) + δ|s|`,

because moving away from the maximizer can gain at most what the penalty charges.  This is the
mechanism that converts a limiting supremum into a pointwise inequality usable in an equation.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The penalized profile. -/
noncomputable def penalized (H : ℝ → ℝ) (δ L₀ L : ℝ) : ℝ := H L - δ * |L - L₀|

/-- **The one-sided inequality at a penalized maximizer.**  Moving away from a maximizer of the
penalized profile can gain at most the penalty charge, so the profile itself is one-sided Lipschitz
there with constant `δ`. -/
theorem le_of_isMaxOn_penalized {H : ℝ → ℝ} {δ L₀ X : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized H δ L₀) s X) (hδ : 0 ≤ δ) {y : ℝ} (hy : y ∈ s) :
    H y ≤ H X + δ * |y - X| := by
  have hle : penalized H δ L₀ y ≤ penalized H δ L₀ X := hmax hy
  unfold penalized at hle
  have htri : |y - L₀| - |X - L₀| ≤ |y - X| := by
    have h := abs_sub_abs_le_abs_sub (y - L₀) (X - L₀)
    rwa [show (y - L₀) - (X - L₀) = y - X by ring] at h
  have hpen : δ * |y - L₀| - δ * |X - L₀| ≤ δ * |y - X| := by
    nlinarith [htri, hδ]
  linarith

/-- The one-sided inequality in the two-sided form the transport argument consumes: at a penalized
maximizer, symmetric increments are dominated by the penalty slope times the shift. -/
theorem le_of_isMaxOn_penalized_shift {H : ℝ → ℝ} {δ L₀ X : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized H δ L₀) s X) (hδ : 0 ≤ δ) {t : ℝ} (ht : 0 ≤ t)
    (hp : X + t ∈ s) (hm : X - t ∈ s) :
    H (X + t) ≤ H X + δ * t ∧ H (X - t) ≤ H X + δ * t := by
  constructor
  · have h := le_of_isMaxOn_penalized hmax hδ hp
    rwa [show X + t - X = t by ring, abs_of_nonneg ht] at h
  · have h := le_of_isMaxOn_penalized hmax hδ hm
    rwa [show X - t - X = -t by ring, abs_neg, abs_of_nonneg ht] at h

/-! ## Existence of the maximizer

The penalty drives the sum to `−∞`, so beyond a computable radius the penalized profile is below
its value at the left endpoint.  The supremum is therefore attained on a compact subinterval, and
that maximizer is global on the whole ray.
-/

/-- **A penalized bounded profile attains its maximum on a ray.**  The penalty forces the profile
below its endpoint value beyond a finite radius, so a compact maximum is a global one. -/
theorem exists_isMaxOn_penalized {H : ℝ → ℝ} {δ L₀ a B : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn H (Ici a)) (hB : ∀ L ∈ Ici a, H L ≤ B) :
    ∃ X ∈ Ici a, IsMaxOn (penalized H δ L₀) (Ici a) X := by
  set Φ := penalized H δ L₀ with hΦ
  have hΦcont : ContinuousOn Φ (Ici a) := by
    rw [hΦ]
    unfold penalized
    exact hcont.sub (continuous_const.mul ((continuous_id.sub continuous_const).abs)).continuousOn
  set R : ℝ := max a (L₀ + (B - Φ a) / δ + 1) with hR
  have haR : a ≤ R := le_max_left _ _
  have hcompact : IsCompact (Icc a R) := isCompact_Icc
  have hne : (Icc a R).Nonempty := ⟨a, ⟨le_refl a, haR⟩⟩
  obtain ⟨X, hXmem, hXmax⟩ :=
    hcompact.exists_isMaxOn hne (hΦcont.mono fun x hx => hx.1)
  refine ⟨X, hXmem.1, fun L hL => ?_⟩
  rcases le_or_gt L R with hLR | hLR
  · exact hXmax ⟨hL, hLR⟩
  · have hfar : Φ L < Φ a := by
      have h1 : L₀ + (B - Φ a) / δ + 1 ≤ R := le_max_right _ _
      have h2 : L₀ + (B - Φ a) / δ < L := by linarith
      have h3 : (B - Φ a) / δ < L - L₀ := by linarith
      have h4 : B - Φ a < δ * (L - L₀) := by
        rw [div_lt_iff₀ hδ] at h3
        linarith
      have h5 : L - L₀ ≤ |L - L₀| := le_abs_self _
      have h6 : H L ≤ B := hB L hL
      have hval : Φ L = H L - δ * |L - L₀| := rfl
      nlinarith [h4, h5, h6, hδ]
    have haIcc : a ∈ Icc a R := ⟨le_refl a, haR⟩
    exact le_of_lt (lt_of_lt_of_le hfar (hXmax haIcc))

/-! ## Localisation of the maximizer

Comparing the maximizer against the base point costs nothing on the penalty side, since the penalty
vanishes there.  So the maximizer's value exceeds the base value by at least the penalty it pays,
and the displacement is bounded by the value gap over the penalty slope.
-/

/-- **The maximizer pays for its displacement.**  Its value exceeds the base value by at least the
penalty charged for moving there. -/
theorem le_penalized_of_isMaxOn {H : ℝ → ℝ} {δ L₀ X : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized H δ L₀) s X) (hL₀ : L₀ ∈ s) :
    H L₀ + δ * |X - L₀| ≤ H X := by
  have h : penalized H δ L₀ L₀ ≤ penalized H δ L₀ X := hmax hL₀
  unfold penalized at h
  rw [sub_self, abs_zero, mul_zero, sub_zero] at h
  linarith

/-- **Localisation.**  The displacement of the maximizer is bounded by the value gap divided by
the penalty slope.  With slope `L₀^{-1/2}` and a bounded profile this is the card's
`|X − L₀| = O(√L₀)`. -/
theorem abs_sub_isMaxOn_penalized_le {H : ℝ → ℝ} {δ L₀ X B : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized H δ L₀) s X) (hδ : 0 < δ) (hL₀ : L₀ ∈ s)
    (hB : H X ≤ B) : |X - L₀| ≤ (B - H L₀) / δ := by
  have h := le_penalized_of_isMaxOn hmax hL₀
  rw [le_div_iff₀ hδ]
  nlinarith [h, hB]

/-! ## Value and interiority at the maximizer

Two immediate consequences of localisation: the maximizer's value dominates the base value, and a
maximizer localised near a base point that is far inside the ray is itself interior.
-/

/-- The maximizer's value dominates the base value. -/
theorem le_value_of_isMaxOn_penalized {H : ℝ → ℝ} {δ L₀ X : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized H δ L₀) s X) (hδ : 0 ≤ δ) (hL₀ : L₀ ∈ s) :
    H L₀ ≤ H X := by
  have h := le_penalized_of_isMaxOn hmax hL₀
  have hpen : 0 ≤ δ * |X - L₀| := mul_nonneg hδ (abs_nonneg _)
  linarith

/-- **Interiority.**  A maximizer localised within `D` of a base point that sits more than `D`
inside the ray is itself interior, so both `X ± t` remain available for small `t`. -/
theorem lt_of_localised {L₀ X D a : ℝ} (hloc : |X - L₀| ≤ D) (hgap : a < L₀ - D) : a < X := by
  have h := abs_le.mp hloc
  linarith [h.1]

/-! ## Removing the square-root weight

The penalized inequalities are stated for the weighted profile `√L f(L)`, while the transport
operator acts on `f` itself.  Moving the weight across costs the ratio of the two square roots.
Forward in `L` that ratio is at most one, so the conversion is free; backward it is not, which is
the same weight mismatch that rules out a uniform modulus.
-/

/-- **Forward weight removal.**  A one-sided bound on the weighted profile gives one on the profile
itself, with the penalty slope divided by `√X`.  Forward in `L` the square-root ratio is at most
one, so nothing is lost. -/
theorem le_of_weighted_le_forward {f : ℝ → ℝ} {X s δ : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hδ : 0 ≤ δ) (hf : 0 ≤ f X)
    (hw : Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s) :
    f (X + s) ≤ f X + δ * s / Real.sqrt X := by
  have hXs : 0 < X + s := by linarith
  have hsq : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hsq' : 0 < Real.sqrt (X + s) := Real.sqrt_pos.mpr hXs
  have hmono : Real.sqrt X ≤ Real.sqrt (X + s) := Real.sqrt_le_sqrt (by linarith)
  have hnum : 0 ≤ Real.sqrt X * f X + δ * s := by positivity
  have hstep : f (X + s) ≤ (Real.sqrt X * f X + δ * s) / Real.sqrt (X + s) := by
    rw [le_div_iff₀ hsq']
    linarith [hw]
  have hstep2 : (Real.sqrt X * f X + δ * s) / Real.sqrt (X + s)
      ≤ (Real.sqrt X * f X + δ * s) / Real.sqrt X :=
    div_le_div_of_nonneg_left hnum hsq hmono
  have hval : (Real.sqrt X * f X + δ * s) / Real.sqrt X = f X + δ * s / Real.sqrt X := by
    field_simp
  linarith [hstep, hstep2, hval.le, hval.ge]

/-! ## The sharp square-root expansion

Backward weight removal needs more than a constant factor: a bound `f(X−s) ≤ √2 (…)` leaves a term
proportional to `f(X)` that does not vanish, so the second difference is not controlled.  The sharp
expansion `(1−u)^{−1/2} ≤ 1 + 2u` on `u ≤ 1/2` is what makes the backward term differ from the
forward one by `O(s/X)` rather than by a constant.
-/

/-- **The sharp expansion.**  `(1 − u)^{−1/2} ≤ 1 + 2u` for `0 ≤ u ≤ 1/2`.  Equivalent to
`u(4u² − 3) ≤ 0` after squaring, which holds since `4u² ≤ 1 < 3` on that range. -/
theorem inv_sqrt_one_sub_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1/2) :
    (Real.sqrt (1 - u))⁻¹ ≤ 1 + 2 * u := by
  have hpos : (0:ℝ) < 1 - u := by linarith
  have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (1 - u) ^ 2 = 1 - u := Real.sq_sqrt hpos.le
  have hle1 : Real.sqrt (1 - u) ≤ 1 := by
    nlinarith [hsq, hs]
  rw [inv_eq_one_div, div_le_iff₀ hs]
  nlinarith [hsq, hs, hle1]

/-- **Backward weight removal.**  Going backward the square-root ratio exceeds one, and the sharp
expansion keeps the excess proportional to `s/X` rather than a constant — which is what leaves the
second difference controlled. -/
theorem le_of_weighted_le_backward {f : ℝ → ℝ} {X s δ : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hδ : 0 ≤ δ) (hf : 0 ≤ f X)
    (hw : Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    f (X - s) ≤ (f X + δ * s / Real.sqrt X) * (1 + 2 * (s / X)) := by
  have hsq : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hu0 : 0 ≤ s / X := div_nonneg hs hX.le
  have hu1 : s / X ≤ 1 / 2 := by rw [div_le_div_iff₀ hX (by norm_num : (0:ℝ) < 2)]; linarith
  have hone : (0:ℝ) < 1 - s / X := by linarith
  have hrs : 0 < Real.sqrt (1 - s / X) := Real.sqrt_pos.mpr hone
  have hprod : X * (1 - s / X) = X - s := by field_simp
  have hfac : Real.sqrt (X - s) = Real.sqrt X * Real.sqrt (1 - s / X) := by
    rw [← hprod, Real.sqrt_mul hX.le]
  have hXs : 0 < Real.sqrt (X - s) := by rw [hfac]; positivity
  have hnum : 0 ≤ f X + δ * s / Real.sqrt X := by positivity
  have hstep : f (X - s) ≤ (Real.sqrt X * f X + δ * s) / Real.sqrt (X - s) := by
    rw [le_div_iff₀ hXs]
    linarith [hw]
  have hval : (Real.sqrt X * f X + δ * s) / Real.sqrt (X - s)
      = (f X + δ * s / Real.sqrt X) * (Real.sqrt (1 - s / X))⁻¹ := by
    rw [hfac]
    field_simp
  rw [hval] at hstep
  have hinv := inv_sqrt_one_sub_le hu0 hu1
  calc f (X - s) ≤ (f X + δ * s / Real.sqrt X) * (Real.sqrt (1 - s / X))⁻¹ := hstep
    _ ≤ (f X + δ * s / Real.sqrt X) * (1 + 2 * (s / X)) :=
        mul_le_mul_of_nonneg_left hinv hnum

/-! ## The mirrored chain

The lower limit needs the same construction applied to the negated profile: a penalized *minimum*
of `H` is a penalized maximum of `−H`.  Stating the mirrored results in terms of
`penalized (−H)` lets the whole maximum apparatus be reused with the inequalities flipped once, at
the point of use, rather than duplicated.
-/

/-- **The mirrored one-sided inequalities.**  At a penalized maximizer of `−H`, the profile `H`
drops by at most `δ t` in either direction — the reverse of the maximizer case. -/
theorem le_of_isMaxOn_penalized_neg_shift {H : ℝ → ℝ} {δ L₀ X : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized (fun x => -H x) δ L₀) s X) (hδ : 0 ≤ δ) {t : ℝ} (ht : 0 ≤ t)
    (hp : X + t ∈ s) (hm : X - t ∈ s) :
    H X - δ * t ≤ H (X + t) ∧ H X - δ * t ≤ H (X - t) := by
  obtain ⟨h1, h2⟩ := le_of_isMaxOn_penalized_shift hmax hδ ht hp hm
  exact ⟨by linarith [h1], by linarith [h2]⟩

/-- **The mirrored maximizer exists**, for a profile bounded below. -/
theorem exists_isMaxOn_penalized_neg {H : ℝ → ℝ} {δ L₀ a B : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn H (Ici a)) (hB : ∀ L ∈ Ici a, -B ≤ H L) :
    ∃ X ∈ Ici a, IsMaxOn (penalized (fun x => -H x) δ L₀) (Ici a) X := by
  refine exists_isMaxOn_penalized (B := B) hδ hcont.neg fun L hL => ?_
  have := hB L hL
  linarith

/-! ## Auxiliary expansions for the mirrored direction

The maximizer direction needed `(1−u)^{−1/2} ≤ 1 + 2u`.  The minimizer direction divides by the
*larger* root instead, so it needs the two companion estimates below: the square root of `1+u` is
at most `1 + u/2`, and the reciprocal of `1+u` is at least `1−u`.
-/

/-- `√(1+u) ≤ 1 + u/2` for `u ≥ 0`; squaring gives `1 + u ≤ 1 + u + u²/4`. -/
theorem sqrt_one_add_le {u : ℝ} (hu : 0 ≤ u) : Real.sqrt (1 + u) ≤ 1 + u / 2 := by
  have h1 : (0:ℝ) ≤ 1 + u := by linarith
  have h2 : (0:ℝ) ≤ 1 + u / 2 := by linarith
  rw [show (1 : ℝ) + u / 2 = Real.sqrt ((1 + u / 2) ^ 2) by
    rw [Real.sqrt_sq h2]]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [sq_nonneg u]

/-- `1 − u ≤ (1+u)⁻¹` for `u ≥ 0`; clearing the denominator gives `1 − u² ≤ 1`. -/
theorem one_sub_le_inv_one_add {u : ℝ} (hu : 0 ≤ u) : 1 - u ≤ (1 + u)⁻¹ := by
  have hpos : (0:ℝ) < 1 + u := by linarith
  have h : (1 - u) * (1 + u) ≤ 1 := by nlinarith [sq_nonneg u]
  have hd : (1 - u) * (1 + u) / (1 + u) ≤ 1 / (1 + u) := by gcongr
  rw [mul_div_assoc, div_self (ne_of_gt hpos), mul_one, one_div] at hd
  exact hd

/-- **Mirrored forward weight removal.**  From a *lower* bound on the weighted profile, a lower
bound on the profile itself, with the correction `1 − s/(2X)` supplied by `sqrt_one_add_le` and
`one_sub_le_inv_one_add`.  The nonnegativity of `f X − δs/√X` is what lets the division reverse the
inequality correctly. -/
theorem le_of_weighted_ge_forward {f : ℝ → ℝ} {X s δ : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hnum : 0 ≤ f X - δ * s / Real.sqrt X)
    (hw : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s)) :
    (f X - δ * s / Real.sqrt X) * (1 - s / (2 * X)) ≤ f (X + s) := by
  have hsq : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hu : 0 ≤ s / X := div_nonneg hs hX.le
  have hprod : X * (1 + s / X) = X + s := by field_simp
  have hfac : Real.sqrt (X + s) = Real.sqrt X * Real.sqrt (1 + s / X) := by
    rw [← hprod, Real.sqrt_mul hX.le]
  have hXs : 0 < Real.sqrt (X + s) := by rw [hfac]; positivity
  have hroot : Real.sqrt (1 + s / X) ≤ 1 + s / (2 * X) := by
    have h := sqrt_one_add_le hu
    have : s / X / 2 = s / (2 * X) := by ring
    linarith [h, this.le, this.ge]
  have hnum' : 0 ≤ Real.sqrt X * f X - δ * s := by
    have : Real.sqrt X * (f X - δ * s / Real.sqrt X) = Real.sqrt X * f X - δ * s := by
      field_simp
    nlinarith [hnum, hsq, this]
  have hdiv : (Real.sqrt X * f X - δ * s) / Real.sqrt (X + s) ≤ f (X + s) := by
    rw [div_le_iff₀ hXs]
    linarith [hw]
  have hbig : Real.sqrt (X + s) ≤ Real.sqrt X * (1 + s / (2 * X)) := by
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hroot hsq.le
  have hupos : 0 < 1 + s / (2 * X) := by positivity
  have hlower : (f X - δ * s / Real.sqrt X) / (1 + s / (2 * X))
      ≤ (Real.sqrt X * f X - δ * s) / Real.sqrt (X + s) := by
    have heq : (Real.sqrt X * f X - δ * s) = Real.sqrt X * (f X - δ * s / Real.sqrt X) := by
      field_simp
    rw [heq, hfac]
    rw [div_le_div_iff₀ hupos (by positivity)]
    have hstep : Real.sqrt (1 + s / X) ≤ 1 + s / (2 * X) := hroot
    nlinarith [hnum, hsq, hstep, Real.sqrt_nonneg (1 + s / X)]
  have hfin : (f X - δ * s / Real.sqrt X) * (1 - s / (2 * X))
      ≤ (f X - δ * s / Real.sqrt X) / (1 + s / (2 * X)) := by
    rw [div_eq_mul_inv]
    have hinv := one_sub_le_inv_one_add (u := s / (2 * X)) (by positivity)
    exact mul_le_mul_of_nonneg_left hinv hnum
  linarith [hfin, hlower, hdiv]

/-- **Mirrored backward weight removal.**  Going backward from a lower bound the square-root ratio
works *for* the estimate — dividing by the smaller root only increases a nonnegative quotient — so
no correction term appears at all:  `f X − δ s/√X ≤ f(X − s)`. -/
theorem le_of_weighted_ge_backward {f : ℝ → ℝ} {X s δ : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hnum : 0 ≤ f X - δ * s / Real.sqrt X)
    (hw : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    f X - δ * s / Real.sqrt X ≤ f (X - s) := by
  have hsq : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hXs0 : 0 < X - s := by linarith
  have hXs : 0 < Real.sqrt (X - s) := Real.sqrt_pos.mpr hXs0
  have hmono : Real.sqrt (X - s) ≤ Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
  have hnum' : 0 ≤ Real.sqrt X * f X - δ * s := by
    have heq : Real.sqrt X * (f X - δ * s / Real.sqrt X) = Real.sqrt X * f X - δ * s := by
      field_simp
    nlinarith [hnum, hsq, heq]
  have hdiv : (Real.sqrt X * f X - δ * s) / Real.sqrt (X - s) ≤ f (X - s) := by
    rw [div_le_iff₀ hXs]
    linarith [hw]
  have hge : (Real.sqrt X * f X - δ * s) / Real.sqrt X
      ≤ (Real.sqrt X * f X - δ * s) / Real.sqrt (X - s) :=
    div_le_div_of_nonneg_left hnum' hXs hmono
  have hval : (Real.sqrt X * f X - δ * s) / Real.sqrt X = f X - δ * s / Real.sqrt X := by
    field_simp
  linarith [hdiv, hge, hval.le, hval.ge]

/-! ## Localisation at the card's slope

Taking the penalty slope to be `L₀^{−1/2}` turns the abstract localisation into the displacement
bound the transport argument needs: the maximizer sits within `√L₀` times the value gap of the base
point, i.e. `O(√L₀)` whenever the profile's values there converge.
-/

/-- **Localisation at slope `1/√L₀`.**  `|X − L₀| ≤ √L₀ (B − H L₀)` — the card's `O(√L₀)`. -/
theorem abs_sub_le_sqrt_mul_of_isMaxOn {H : ℝ → ℝ} {L₀ X B : ℝ} {s : Set ℝ} (hL₀ : 0 < L₀)
    (hmax : IsMaxOn (penalized H (Real.sqrt L₀)⁻¹ L₀) s X) (hL₀mem : L₀ ∈ s) (hB : H X ≤ B) :
    |X - L₀| ≤ Real.sqrt L₀ * (B - H L₀) := by
  have hsq : 0 < Real.sqrt L₀ := Real.sqrt_pos.mpr hL₀
  have hδ : 0 < (Real.sqrt L₀)⁻¹ := by positivity
  have h := abs_sub_isMaxOn_penalized_le hmax hδ hL₀mem hB
  have hrw : (B - H L₀) / (Real.sqrt L₀)⁻¹ = Real.sqrt L₀ * (B - H L₀) := by
    field_simp
  rw [hrw] at h
  exact h

/-! ## The maximizer runs to infinity

Localisation puts the maximizer within `K√L₀` of the base point, so it is at least `L₀ − K√L₀`,
which tends to infinity with `L₀`.  Hence every quantity that vanishes at infinity vanishes along
the family of maximizers.
-/

open Filter in
/-- **`L − K√L → ∞`.**  Factoring as `√L(√L − K)`, both factors tend to infinity. -/
theorem tendsto_sub_const_mul_sqrt_atTop (K : ℝ) :
    Tendsto (fun L : ℝ => L - K * Real.sqrt L) atTop atTop := by
  have hs : Tendsto (fun L : ℝ => Real.sqrt L) atTop atTop := Real.tendsto_sqrt_atTop
  have hsk : Tendsto (fun L : ℝ => Real.sqrt L - K) atTop atTop :=
    tendsto_atTop_add_const_right _ (-K) hs
  have hprod : Tendsto (fun L : ℝ => Real.sqrt L * (Real.sqrt L - K)) atTop atTop :=
    hs.atTop_mul_atTop₀ hsk
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL
  nlinarith [hsq]

end GaloisForLFunctions.HTGeometry
