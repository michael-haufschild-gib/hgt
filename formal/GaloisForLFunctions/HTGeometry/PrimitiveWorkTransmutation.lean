import GaloisForLFunctions.HTGeometry.ReflectionContactParity

/-!
# Primitive-work character transmutation

For an even positive analytic response `I` of order `2k` and `c > 0`, the current
`C_I(t) = ∫₀ᵗ I` and the reflected work `W_I(t) = c t C_I(t)` `(PW.2)` satisfy:

* **Theorem 1.1, `(PW.3)`–`(PW.5)`.**  `C_I` is odd of order `2k + 1`, `W_I` is even, nonnegative
  and of order `2k + 2`.  The normalized analytic roots `q = tᵏ·(unit)`, `q² = I - W_I` and
  `w = t^{k+1}·(unit)`, `w² = W_I` exist, are unique, and have opposite reflection characters
  `(-1)ᵏ` and `(-1)^{k+1}`.  The order of a primitive is computed by differentiating the contact
  factorization `F = t^j G`: `F' = t^{j-1}(j G + t G')`.
* **Theorem 2.1, `(PW.9)`–`(PW.11)`.**  `v = (q, w)` has `‖v‖² = I`, and `Γ = ∫ v` is an oriented
  realization with involution `R_k = diag((-1)^{k+1}, (-1)^{k+2})`; for odd `k` the reflected
  channel's energy is exactly the work `W_I`.
* **Corollary 3.1.**  The marked pair `(I, W_I)` reconstructs `(q, w)`, while `I` alone admits
  infinitely many distinct analytic velocities `q (cos st, sin st)` of the same norm.
-/

open Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {I : ℝ → ℝ} {k : ℕ}

/-! ### The contact of a primitive -/

/-- **The primitive raises contact order by one**: if `f = tᵐ·(unit)` with leading coefficient `a`,
then `∫₀ᵗ f = t^{m+1}·(unit)` with leading coefficient `a/(m+1)`. -/
theorem AnalyticContact.primitive {f : ℝ → ℝ} {m : ℕ} {a : ℝ} (hf : AnalyticContact f m a) :
    AnalyticContact (primitiveAtZero f) (m + 1) (a / (m + 1)) := by
  have hfa := hf.analyticAt
  have hFa := analyticAt_primitiveAtZero hfa
  have hdF : deriv (primitiveAtZero f) =ᶠ[𝓝 0] f :=
    (eventually_hasDerivAt_primitiveAtZero hfa).mono fun t ht => ht.deriv
  have hFne : ¬ ∀ᶠ t in 𝓝 0, primitiveAtZero f t = 0 := by
    intro h
    have h0 : (primitiveAtZero f) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := h
    have hf0 : ∀ᶠ t in 𝓝 0, f t = 0 := by
      filter_upwards [hdF, h0.deriv] with t h1 h2
      rw [← h1, h2, deriv_const]
    have htop := analyticOrderAt_eq_top.mpr hf0
    rw [hf.analyticOrderAt_eq] at htop
    exact ENat.coe_ne_top _ htop
  obtain ⟨j, b, G, hG, hG0, hb, hfac⟩ := exists_analyticContact hFa hFne
  have hj : 0 < j := AnalyticContact.order_pos_of_value_zero
    (show AnalyticContact (primitiveAtZero f) j b from ⟨G, hG, hG0, hb, hfac⟩)
    (primitiveAtZero_zero f)
  have hfac' : primitiveAtZero f =ᶠ[𝓝 0] fun t => t ^ j * G t := by
    filter_upwards [hfac] with t ht
    simpa [smul_eq_mul] using ht
  have hd : AnalyticContact f (j - 1) (j * b) := by
    refine ⟨fun t => j * G t + t * deriv G t, (analyticAt_const.mul hG).add
      (analyticAt_id.mul hG.deriv), by simp [hG0], mul_ne_zero (by exact_mod_cast hj.ne') hb, ?_⟩
    filter_upwards [hdF, hfac'.deriv, hG.eventually_analyticAt] with t h1 h2 h3
    rw [← h1, h2, smul_eq_mul]
    have hpow : HasDerivAt (fun t : ℝ => t ^ j) (j * t ^ (j - 1)) t := by
      simpa using hasDerivAt_pow j t
    have hprod : HasDerivAt (fun t => t ^ j * G t) (j * t ^ (j - 1) * G t + t ^ j * deriv G t) t :=
      hpow.mul h3.differentiableAt.hasDerivAt
    rw [hprod.deriv]
    have ht : t ^ j = t ^ (j - 1) * t := by
      rw [← pow_succ, Nat.sub_add_cancel hj]
    rw [ht]
    ring
  have hm : m = j - 1 := by
    have h1 := hf.analyticOrderAt_eq
    rw [hd.analyticOrderAt_eq] at h1
    exact_mod_cast h1.symm
  have hlead : a = j * b := hf.leading_eq (hm ▸ hd)
  have hj' : j = m + 1 := by omega
  subst hj'
  have hb' : b = a / (m + 1) := by
    rw [hlead]
    push_cast
    field_simp
  exact ⟨G, hG, hG0.trans hb', hb' ▸ hb, hfac⟩

/-! ### Normalized analytic roots -/

/-- `r` is a normalized analytic root of `g` of order `j` `(PW.4)`: `r = tʲ H` near `0` with `H`
analytic and `H(0) > 0`, and `r² = g` near `0`. -/
def IsNormalizedRoot (g : ℝ → ℝ) (j : ℕ) (r : ℝ → ℝ) : Prop :=
  ∃ H : ℝ → ℝ, AnalyticAt ℝ H 0 ∧ 0 < H 0 ∧ (∀ᶠ t in 𝓝 0, r t = t ^ j * H t) ∧
    ∀ᶠ t in 𝓝 0, r t ^ 2 = g t

theorem analyticAt_sqrt_comp {U : ℝ → ℝ} (hU : AnalyticAt ℝ U 0) (hU0 : 0 < U 0) :
    AnalyticAt ℝ (fun t => Real.sqrt (U t)) 0 := by
  have hupos : ∀ᶠ t in 𝓝 0, 0 < U t :=
    (hU.continuousAt : Tendsto U (𝓝 0) (𝓝 (U 0))).eventually_const_lt hU0
  have hg : AnalyticAt ℝ (fun t => Real.exp (Real.log (U t) * (1 / 2))) 0 :=
    analyticAt_rexp.comp (((analyticAt_log hU0).comp hU).mul analyticAt_const)
  refine hg.congr ?_
  filter_upwards [hupos] with t ht
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]

namespace IsNormalizedRoot

variable {g r r' : ℝ → ℝ} {j : ℕ}

theorem analyticAt (h : IsNormalizedRoot g j r) : AnalyticAt ℝ r 0 := by
  obtain ⟨H, hH, -, hr, -⟩ := h
  exact ((analyticAt_id.pow j).mul hH).congr (EventuallyEq.symm hr)

theorem pos_right (h : IsNormalizedRoot g j r) : ∀ᶠ t in 𝓝[>] 0, 0 < r t := by
  obtain ⟨H, hH, hH0, hr, -⟩ := h
  have hHpos : ∀ᶠ t in 𝓝 0, 0 < H t :=
    (hH.continuousAt : Tendsto H (𝓝 0) (𝓝 (H 0))).eventually_const_lt hH0
  filter_upwards [nhdsWithin_le_nhds (hr.and hHpos), self_mem_nhdsWithin] with t ⟨h1, h2⟩ ht
  rw [h1]
  exact mul_pos (pow_pos ht j) h2

/-- **Uniqueness of normalized roots.** -/
theorem unique (h : IsNormalizedRoot g j r) (h' : IsNormalizedRoot g j r') : r =ᶠ[𝓝 0] r' := by
  have hsq : ∀ᶠ t in 𝓝 0, r t ^ 2 = r' t ^ 2 := by
    obtain ⟨_, _, _, _, hs⟩ := h
    obtain ⟨_, _, _, _, hs'⟩ := h'
    filter_upwards [hs, hs'] with t h1 h2
    rw [h1, h2]
  rcases eventuallyEq_or_eventuallyEq_neg_of_sq_eq h.analyticAt h'.analyticAt hsq with he | he
  · exact he
  · exfalso
    obtain ⟨t, h1, h2, h3⟩ := (h.pos_right.and (h'.pos_right.and (nhdsWithin_le_nhds he))).exists
    linarith

/-- **The character of a normalized root of an even germ is `(-1)ʲ`.** -/
theorem character (h : IsNormalizedRoot g j r) (heven : ∀ᶠ t in 𝓝 0, g (-t) = g t) :
    ∀ᶠ t in 𝓝 0, r (-t) = (-1) ^ j * r t := by
  obtain ⟨H, hH, hH0, hr, hsq⟩ := h
  have hrefl : IsNormalizedRoot g j (fun t => (-1) ^ j * r (-t)) := by
    refine ⟨fun t => H (-t), ?_, by simpa using hH0, ?_, ?_⟩
    · have hH' : AnalyticAt ℝ H (-0) := by simpa using hH
      exact hH'.comp analyticAt_id.neg
    · filter_upwards [eventually_neg_of_eventually hr] with t ht
      rw [ht, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
    · filter_upwards [eventually_neg_of_eventually hsq, heven] with t h1 h2
      rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul, neg_one_sq, one_pow, one_mul, h1, h2]
  have hu := hrefl.unique ⟨H, hH, hH0, hr, hsq⟩
  filter_upwards [hu] with t ht
  rw [← ht, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end IsNormalizedRoot

/-- **Existence of normalized roots**: `g = t^{2j} U` with `U` analytic and `U(0) > 0` has the
normalized root `tʲ √U`. -/
theorem exists_normalizedRoot {g U : ℝ → ℝ} {j : ℕ} (hU : AnalyticAt ℝ U 0) (hU0 : 0 < U 0)
    (hfac : ∀ᶠ t in 𝓝 0, g t = t ^ (2 * j) * U t) : ∃ r, IsNormalizedRoot g j r := by
  have hupos : ∀ᶠ t in 𝓝 0, 0 < U t :=
    (hU.continuousAt : Tendsto U (𝓝 0) (𝓝 (U 0))).eventually_const_lt hU0
  refine ⟨fun t => t ^ j * Real.sqrt (U t), fun t => Real.sqrt (U t), analyticAt_sqrt_comp hU hU0,
    Real.sqrt_pos.mpr hU0, Eventually.of_forall fun t => rfl, ?_⟩
  filter_upwards [hfac, hupos] with t ht hpos
  rw [ht, mul_pow, Real.sq_sqrt hpos.le, ← pow_mul, mul_comm j 2]

/-! ### Theorem 1.1 -/

/-- The reflected work `W_I(t) = c t ∫₀ᵗ I` `(PW.2)`. -/
def reflectedWork (c : ℝ) (I : ℝ → ℝ) (t : ℝ) : ℝ := c * t * primitiveAtZero I t

namespace EvenPositiveResponse

/-- **The current is odd.** -/
theorem current_odd (hI : EvenPositiveResponse I k) :
    ∀ᶠ t in 𝓝 0, primitiveAtZero I (-t) = -primitiveAtZero I t :=
  primitiveAtZero_neg_of_even hI.even

/-- **The work is even.** -/
theorem work_even (hI : EvenPositiveResponse I k) (c : ℝ) :
    ∀ᶠ t in 𝓝 0, reflectedWork c I (-t) = reflectedWork c I t := by
  filter_upwards [hI.current_odd] with t ht
  rw [reflectedWork, reflectedWork, ht]
  ring

/-- **The work is nonnegative.** -/
theorem work_nonneg (hI : EvenPositiveResponse I k) {c : ℝ} (hc : 0 ≤ c) :
    ∀ᶠ t in 𝓝 0, 0 ≤ reflectedWork c I t := by
  have hpos : ∀ᶠ t in 𝓝 0, 0 ≤ t → 0 ≤ primitiveAtZero I t := by
    filter_upwards [eventually_forall_uIcc hI.nonneg] with t ht ht0
    exact intervalIntegral.integral_nonneg ht0 fun s hs => ht s (by
      rw [uIcc_of_le ht0]
      exact hs)
  filter_upwards [hpos, eventually_neg_of_eventually hpos, hI.current_odd] with t h1 h2 h3
  rcases le_total 0 t with ht | ht
  · exact mul_nonneg (mul_nonneg hc ht) (h1 ht)
  · have := h2 (neg_nonneg.mpr ht)
    rw [h3] at this
    rw [reflectedWork]
    exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc ht) (by linarith)

/-- The contact data of the response, current and work. -/
theorem contacts (hI : EvenPositiveResponse I k) :
    ∃ u V : ℝ → ℝ, AnalyticAt ℝ u 0 ∧ 0 < u 0 ∧ (∀ᶠ t in 𝓝 0, u (-t) = u t) ∧
      (∀ᶠ t in 𝓝 0, I t = t ^ (2 * k) * u t) ∧ AnalyticAt ℝ V 0 ∧
      V 0 = u 0 / (2 * k + 1) ∧ (∀ᶠ t in 𝓝 0, V (-t) = V t) ∧
      ∀ᶠ t in 𝓝 0, primitiveAtZero I t = t ^ (2 * k + 1) * V t := by
  obtain ⟨u, hu, hu0, hueven, hfac⟩ := hI.exists_unit
  have hcI : AnalyticContact I (2 * k) (u 0) :=
    ⟨u, hu, rfl, hu0.ne', by simpa [smul_eq_mul] using hfac⟩
  obtain ⟨V, hV, hV0, -, hVfac⟩ := hcI.primitive
  have hVfac' : ∀ᶠ t in 𝓝 0, primitiveAtZero I t = t ^ (2 * k + 1) * V t := by
    simpa [smul_eq_mul] using hVfac
  refine ⟨u, V, hu, hu0, hueven, hfac, hV, by rw [hV0]; push_cast; ring, ?_, hVfac'⟩
  filter_upwards [hVfac', eventually_neg_of_eventually hVfac', hI.current_odd] with t h1 h2 h3
  by_cases ht : t = 0
  · rw [ht, neg_zero]
  rw [h3, h1, Odd.neg_pow ⟨k, rfl⟩] at h2
  have := mul_left_cancel₀ (pow_ne_zero (2 * k + 1) ht) (by linarith : t ^ (2 * k + 1) * V (-t) =
    t ^ (2 * k + 1) * V t)
  exact this

/-- **Theorem 1.1, `(PW.3)`: `ν(C_I) = 2k + 1`.** -/
theorem analyticOrderAt_current (hI : EvenPositiveResponse I k) :
    analyticOrderAt (primitiveAtZero I) 0 = ((2 * k + 1 : ℕ) : ℕ∞) := by
  obtain ⟨u, V, -, hu0, -, -, hV, hV0, -, hfac⟩ := hI.contacts
  have hc : AnalyticContact (primitiveAtZero I) (2 * k + 1) (V 0) :=
    ⟨V, hV, rfl, by rw [hV0]; positivity, by simpa [smul_eq_mul] using hfac⟩
  exact hc.analyticOrderAt_eq

/-- The work factorization `W_I = t^{2k+2} (c V)`. -/
theorem work_factor (_hI : EvenPositiveResponse I k) (c : ℝ) {V : ℝ → ℝ}
    (hfac : ∀ᶠ t in 𝓝 0, primitiveAtZero I t = t ^ (2 * k + 1) * V t) :
    ∀ᶠ t in 𝓝 0, reflectedWork c I t = t ^ (2 * (k + 1)) * (c * V t) := by
  filter_upwards [hfac] with t ht
  rw [reflectedWork, ht]
  ring

/-- **Theorem 1.1, `(PW.3)`: `ν(W_I) = 2k + 2`.** -/
theorem analyticOrderAt_work (hI : EvenPositiveResponse I k) {c : ℝ} (hc : c ≠ 0) :
    analyticOrderAt (reflectedWork c I) 0 = ((2 * k + 2 : ℕ) : ℕ∞) := by
  obtain ⟨u, V, -, hu0, -, -, hV, hV0, -, hfac⟩ := hI.contacts
  have hcw : AnalyticContact (reflectedWork c I) (2 * (k + 1)) (c * V 0) :=
    ⟨fun t => c * V t, analyticAt_const.mul hV, rfl,
      mul_ne_zero hc (by rw [hV0]; positivity), by simpa [smul_eq_mul] using hI.work_factor c hfac⟩
  rw [hcw.analyticOrderAt_eq]
  congr 1

/-- **Theorem 1.1, `(PW.4)`–`(PW.5)`.**  The normalized roots `q` of `I - W_I` (order `k`) and `w`
of `W_I` (order `k + 1`) exist; every such pair has characters `(-1)ᵏ` and `(-1)^{k+1}`. -/
theorem exists_work_roots (hI : EvenPositiveResponse I k) {c : ℝ} (hc : 0 < c) :
    ∃ q w : ℝ → ℝ, IsNormalizedRoot (fun t => I t - reflectedWork c I t) k q ∧
      IsNormalizedRoot (reflectedWork c I) (k + 1) w := by
  obtain ⟨u, V, hu, hu0, -, hfac, hV, hV0, -, hVfac⟩ := hI.contacts
  have hV0pos : 0 < V 0 := by rw [hV0]; positivity
  obtain ⟨w, hw⟩ := exists_normalizedRoot (analyticAt_const.mul hV) (mul_pos hc hV0pos)
    (hI.work_factor c hVfac)
  obtain ⟨q, hq⟩ := exists_normalizedRoot (g := fun t => I t - reflectedWork c I t) (j := k)
    (U := fun t => u t - c * t ^ 2 * V t)
    (hu.sub ((analyticAt_const.mul (analyticAt_id.pow 2)).mul hV)) (by simpa using hu0) (by
      filter_upwards [hfac, hI.work_factor c hVfac] with t h1 h2
      rw [h1, h2]
      ring)
  exact ⟨q, w, hq, hw⟩

theorem sub_work_even (hI : EvenPositiveResponse I k) (c : ℝ) :
    ∀ᶠ t in 𝓝 0, I (-t) - reflectedWork c I (-t) = I t - reflectedWork c I t := by
  filter_upwards [hI.even, hI.work_even c] with t h1 h2
  rw [h1, h2]

/-- **`(PW.5)`: opposite reflection characters.** -/
theorem work_root_characters (hI : EvenPositiveResponse I k) {c : ℝ} {q w : ℝ → ℝ}
    (hq : IsNormalizedRoot (fun t => I t - reflectedWork c I t) k q)
    (hw : IsNormalizedRoot (reflectedWork c I) (k + 1) w) :
    (∀ᶠ t in 𝓝 0, q (-t) = (-1) ^ k * q t) ∧ ∀ᶠ t in 𝓝 0, w (-t) = (-1) ^ (k + 1) * w t :=
  ⟨hq.character (hI.sub_work_even c), hw.character (hI.work_even c)⟩

end EvenPositiveResponse

/-! ### Theorem 2.1 -/

/-- **Channel realizations.**  An odd velocity on a fixed unit vector and an even velocity, positive
on `(0, δ)`, on an orthogonal reversed unit vector, realize the sum of their squares. -/
theorem exists_channelRealization {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (R : V ≃ₗᵢ[ℝ] V) (hR : ∀ v, R (R v) = v) {uf ur : V} (huf : ‖uf‖ = 1)
    (hur : ‖ur‖ = 1) (horth : ⟪uf, ur⟫_ℝ = 0) (hRf : R uf = uf) (hRr : R ur = -ur)
    {vf vr : ℝ → ℝ} (hvf : AnalyticAt ℝ vf 0) (hvr : AnalyticAt ℝ vr 0)
    (hvf_odd : ∀ᶠ t in 𝓝 0, vf (-t) = -vf t) (hvr_even : ∀ᶠ t in 𝓝 0, vr (-t) = vr t)
    (hvr_pos : ∀ᶠ t in 𝓝[>] 0, 0 < vr t) (hsum : ∀ᶠ t in 𝓝 0, vf t ^ 2 + vr t ^ 2 = I t) :
    ∃ ρ : OrientedRealization I V, ρ.refl = R ∧
      ρ.curve = fun t => primitiveAtZero vf t • uf + primitiveAtZero vr t • ur := by
  have h1even := primitiveAtZero_neg_of_odd hvf_odd
  have h2odd := primitiveAtZero_neg_of_even hvr_even
  have h2sep := eventually_ne_neg_of_pos_of_odd (eventually_primitiveAtZero_pos hvr hvr_pos) h2odd
  refine ⟨{ refl := R
            refl_refl := hR
            curve := fun t => primitiveAtZero vf t • uf + primitiveAtZero vr t • ur
            analyticAt := ((analyticAt_primitiveAtZero hvf).smul analyticAt_const).add
              ((analyticAt_primitiveAtZero hvr).smul analyticAt_const)
            curve_zero := by simp [primitiveAtZero_zero]
            equivariant := ?_
            speed := ?_
            separated := ?_ }, rfl, rfl⟩
  · filter_upwards [h1even, h2odd] with t h1 h2
    simp only [h1, h2, map_add, map_smul, hRf, hRr, neg_smul, smul_neg]
  · filter_upwards [eventually_hasDerivAt_primitiveAtZero hvf,
      eventually_hasDerivAt_primitiveAtZero hvr, hsum] with t hd1 hd2 hst
    have hd : HasDerivAt (fun t => primitiveAtZero vf t • uf + primitiveAtZero vr t • ur)
        (vf t • uf + vr t • ur) t := (hd1.smul_const uf).add (hd2.smul_const ur)
    rw [hd.deriv, norm_smul_add_smul_sq huf hur horth, hst]
  · filter_upwards [h2sep] with t ht heq
    apply ht
    have h := congrArg (fun v => ⟪ur, v⟫_ℝ) heq
    simpa only [inner_smul_add_smul_right hur horth] using h

/-- The coordinate vectors of the plane. -/
abbrev planeE0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

abbrev planeE1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

theorem plane_orthonormal : ‖planeE0‖ = 1 ∧ ‖planeE1‖ = 1 ∧ ⟪planeE0, planeE1⟫_ℝ = 0 := by
  have hon := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 2)
  exact ⟨hon.1 0, hon.1 1, hon.2 (by decide)⟩

/-- `R_k = diag((-1)^{k+1}, (-1)^{k+2})` `(PW.9)`: the reflection fixing the coordinate whose
velocity has odd character. -/
def channelReflection (k : ℕ) : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  if Even k then (ℝ ∙ planeE1).reflection else (ℝ ∙ planeE0).reflection

theorem channelReflection_reflection (k : ℕ) (v : EuclideanSpace ℝ (Fin 2)) :
    channelReflection k (channelReflection k v) = v := by
  unfold channelReflection
  split_ifs <;> exact Submodule.reflection_reflection _ v

theorem planeE1_mem_orthogonal : planeE1 ∈ (ℝ ∙ planeE0)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr plane_orthonormal.2.2

theorem planeE0_mem_orthogonal : planeE0 ∈ (ℝ ∙ planeE1)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (by rw [real_inner_comm]; exact plane_orthonormal.2.2)

theorem channelReflection_e0 (k : ℕ) : channelReflection k planeE0 = (-1) ^ (k + 1) • planeE0 := by
  unfold channelReflection
  split_ifs with hk
  · rw [Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg planeE0_mem_orthogonal,
      pow_succ, hk.neg_one_pow, one_mul, neg_one_smul]
  · rw [Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self _),
      pow_succ, (Nat.not_even_iff_odd.mp hk).neg_one_pow, neg_one_mul, neg_neg, one_smul]

theorem channelReflection_e1 (k : ℕ) : channelReflection k planeE1 = (-1) ^ (k + 2) • planeE1 := by
  unfold channelReflection
  split_ifs with hk
  · rw [Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self _),
      pow_add, hk.neg_one_pow, one_mul, neg_one_sq, one_smul]
  · rw [Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg planeE1_mem_orthogonal,
      pow_add, (Nat.not_even_iff_odd.mp hk).neg_one_pow, neg_one_sq, mul_one, neg_one_smul]

namespace EvenPositiveResponse

/-- **Theorem 2.1, `(PW.9)`–`(PW.11)`: the primitive-work polarization.**  `‖(q, w)‖² = I`, and
`Γ = ∫ (q, w)` is an oriented realization of `I` with involution `R_k`.  For odd `k` the reversed
channel is `w`, whose energy `w²` is the reflected work. -/
theorem primitiveWork_polarization (hI : EvenPositiveResponse I k) {c : ℝ} {q w : ℝ → ℝ}
    (hq : IsNormalizedRoot (fun t => I t - reflectedWork c I t) k q)
    (hw : IsNormalizedRoot (reflectedWork c I) (k + 1) w) :
    (∀ᶠ t in 𝓝 0, ‖q t • planeE0 + w t • planeE1‖ ^ 2 = I t) ∧
      ∃ ρ : OrientedRealization I (EuclideanSpace ℝ (Fin 2)), ρ.refl = channelReflection k ∧
        ρ.curve = fun t => primitiveAtZero q t • planeE0 + primitiveAtZero w t • planeE1 := by
  obtain ⟨hqc, hwc⟩ := hI.work_root_characters hq hw
  obtain ⟨-, -, -, -, hqsq⟩ := id hq
  obtain ⟨-, -, -, -, hwsq⟩ := id hw
  have hsum : ∀ᶠ t in 𝓝 0, q t ^ 2 + w t ^ 2 = I t := by
    filter_upwards [hqsq, hwsq] with t h1 h2
    rw [h1, h2]
    ring
  obtain ⟨h0, h1, h01⟩ := plane_orthonormal
  refine ⟨?_, ?_⟩
  · filter_upwards [hsum] with t ht
    rw [norm_smul_add_smul_sq h0 h1 h01, ht]
  by_cases hk : Even k
  · have hqe : ∀ᶠ t in 𝓝 0, q (-t) = q t := by
      filter_upwards [hqc] with t ht
      rw [ht, hk.neg_one_pow, one_mul]
    have hwo : ∀ᶠ t in 𝓝 0, w (-t) = -w t := by
      filter_upwards [hwc] with t ht
      rw [ht, pow_succ, hk.neg_one_pow, one_mul, neg_one_mul]
    obtain ⟨ρ, hρR, hρc⟩ := exists_channelRealization (I := I) (channelReflection k)
      (channelReflection_reflection k) h1 h0 (by rw [real_inner_comm]; exact h01)
      (by rw [channelReflection_e1, pow_add, hk.neg_one_pow, one_mul, neg_one_sq, one_smul])
      (by rw [channelReflection_e0, pow_succ, hk.neg_one_pow, one_mul, neg_one_smul])
      hw.analyticAt hq.analyticAt hwo hqe hq.pos_right (by
        filter_upwards [hsum] with t ht
        rw [← ht]
        ring)
    refine ⟨ρ, hρR, ?_⟩
    rw [hρc]
    funext t
    exact add_comm _ _
  · have hko : Odd k := Nat.not_even_iff_odd.mp hk
    have hqo : ∀ᶠ t in 𝓝 0, q (-t) = -q t := by
      filter_upwards [hqc] with t ht
      rw [ht, hko.neg_one_pow, neg_one_mul]
    have hwe : ∀ᶠ t in 𝓝 0, w (-t) = w t := by
      filter_upwards [hwc] with t ht
      rw [ht, pow_succ, hko.neg_one_pow, neg_one_mul, neg_neg, one_mul]
    exact exists_channelRealization (I := I) (channelReflection k)
      (channelReflection_reflection k) h0 h1 h01
      (by rw [channelReflection_e0, pow_succ, hko.neg_one_pow, neg_one_mul, neg_neg, one_smul])
      (by rw [channelReflection_e1, pow_add, hko.neg_one_pow, neg_one_sq, mul_one, neg_one_smul])
      hq.analyticAt hw.analyticAt hqo hwe hw.pos_right hsum

end EvenPositiveResponse

/-! ### Corollary 3.1 -/

theorem primitiveAtZero_congr {f g : ℝ → ℝ} (h : f =ᶠ[𝓝 0] g) :
    primitiveAtZero f =ᶠ[𝓝 0] primitiveAtZero g := by
  filter_upwards [eventually_forall_uIcc h] with t ht
  exact intervalIntegral.integral_congr fun s hs => ht s hs

/-- The rotated velocity `q (cos st, sin st)`. -/
def rotatedVelocity (q : ℝ → ℝ) (s t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (q t * Real.cos (s * t)) • planeE0 + (q t * Real.sin (s * t)) • planeE1

namespace EvenPositiveResponse

/-- **Corollary 3.1, reconstruction.**  The marked pair `(I, W_I)` with the positive normalization
determines the roots `(q, w)`, hence the velocity and the curve. -/
theorem work_roots_unique (_hI : EvenPositiveResponse I k) {c : ℝ} {q w q' w' : ℝ → ℝ}
    (hq : IsNormalizedRoot (fun t => I t - reflectedWork c I t) k q)
    (hw : IsNormalizedRoot (reflectedWork c I) (k + 1) w)
    (hq' : IsNormalizedRoot (fun t => I t - reflectedWork c I t) k q')
    (hw' : IsNormalizedRoot (reflectedWork c I) (k + 1) w') :
    q =ᶠ[𝓝 0] q' ∧ w =ᶠ[𝓝 0] w' ∧
      (fun t => primitiveAtZero q t • planeE0 + primitiveAtZero w t • planeE1) =ᶠ[𝓝 0]
        fun t => primitiveAtZero q' t • planeE0 + primitiveAtZero w' t • planeE1 := by
  have h1 := hq.unique hq'
  have h2 := hw.unique hw'
  refine ⟨h1, h2, ?_⟩
  filter_upwards [primitiveAtZero_congr h1, primitiveAtZero_congr h2] with t ht1 ht2
  rw [ht1, ht2]

/-- **Corollary 3.1, `I` alone does not reconstruct.**  For a square root `q` of `I`, every rotated
velocity `q (cos st, sin st)` has squared norm `I`, and distinct `s` give distinct velocity germs:
there are infinitely many. -/
theorem rotatedVelocity_ambiguity (hI : EvenPositiveResponse I k) {q : ℝ → ℝ}
    (hq : AnalyticAt ℝ q 0) (hsq : ∀ᶠ t in 𝓝 0, I t = q t ^ 2) :
    (∀ s : ℝ, ∀ᶠ t in 𝓝 0, ‖rotatedVelocity q s t‖ ^ 2 = I t) ∧
      Function.Injective fun s : ℝ =>
        ((rotatedVelocity q s : ℝ → EuclideanSpace ℝ (Fin 2)) :
          (𝓝 (0 : ℝ)).Germ (EuclideanSpace ℝ (Fin 2))) := by
  obtain ⟨h0, h1, h01⟩ := plane_orthonormal
  refine ⟨fun s => ?_, fun s₁ s₂ hs => ?_⟩
  · filter_upwards [hsq] with t ht
    rw [rotatedVelocity, norm_smul_add_smul_sq h0 h1 h01, ht, mul_pow, mul_pow, ← mul_add,
      Real.cos_sq_add_sin_sq, mul_one]
  · by_contra hne
    have heq : (rotatedVelocity q s₁ : ℝ → EuclideanSpace ℝ (Fin 2)) =ᶠ[𝓝 0]
        rotatedVelocity q s₂ := Filter.Germ.coe_eq.mp hs
    have hq0 : ∀ᶠ t in 𝓝[≠] 0, q t ≠ 0 := by
      rcases hq.eventually_eq_zero_or_eventually_ne_zero with h | h
      · exfalso
        apply hI.not_eventually_zero
        filter_upwards [h, hsq] with t h1 h2
        rw [h2, h1]
        ring
      · exact h
    have hlim1 : Tendsto (fun t : ℝ => (s₁ - s₂) * t / 2) (𝓝 0) (𝓝 0) := by
      have h : Continuous fun t : ℝ => (s₁ - s₂) * t / 2 := by fun_prop
      simpa using h.tendsto (0 : ℝ)
    have hlim2 : Tendsto (fun t : ℝ => (s₁ + s₂) * t / 2) (𝓝 0) (𝓝 0) := by
      have h : Continuous fun t : ℝ => (s₁ + s₂) * t / 2 := by fun_prop
      simpa using h.tendsto (0 : ℝ)
    have hpi : ∀ᶠ t in 𝓝 0, (s₁ - s₂) * t / 2 ∈ Ioo (-Real.pi) Real.pi :=
      hlim1.eventually (Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos)
    have hpi2 : ∀ᶠ t in 𝓝 0, (s₁ + s₂) * t / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      hlim2.eventually (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
    have hall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), rotatedVelocity q s₁ t = rotatedVelocity q s₂ t ∧
        (s₁ - s₂) * t / 2 ∈ Ioo (-Real.pi) Real.pi ∧
        (s₁ + s₂) * t / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      nhdsWithin_le_nhds (heq.and (hpi.and hpi2))
    obtain ⟨t, ⟨⟨ht1, ht2, ht3⟩, ht4⟩, ht0⟩ := ((hall.and hq0).and self_mem_nhdsWithin).exists
    have hsin : Real.sin (s₁ * t) = Real.sin (s₂ * t) := by
      have h := congrArg (fun v => ⟪planeE1, v⟫_ℝ) ht1
      simp only [rotatedVelocity, inner_smul_add_smul_right h1 h01] at h
      exact mul_left_cancel₀ ht4 h
    have hdiff := Real.sin_sub_sin (s₁ * t) (s₂ * t)
    rw [hsin, sub_self] at hdiff
    have hne1 : Real.sin ((s₁ * t - s₂ * t) / 2) ≠ 0 := by
      have harg : (s₁ * t - s₂ * t) / 2 = (s₁ - s₂) * t / 2 := by ring
      rw [harg]
      intro h0'
      have := (Real.sin_eq_zero_iff_of_lt_of_lt ht2.1 ht2.2).mp h0'
      have ht0' : t ≠ 0 := ht0
      have hs' : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
      exact mul_ne_zero (mul_ne_zero hs' ht0') two_ne_zero (by linarith)
    have hne2 : Real.cos ((s₁ * t + s₂ * t) / 2) ≠ 0 := by
      have harg : (s₁ * t + s₂ * t) / 2 = (s₁ + s₂) * t / 2 := by ring
      rw [harg]
      exact (Real.cos_pos_of_mem_Ioo ht3).ne'
    exact (mul_ne_zero (mul_ne_zero two_ne_zero hne1) hne2) hdiff.symm

end EvenPositiveResponse

end GaloisForLFunctions.HTGeometry
