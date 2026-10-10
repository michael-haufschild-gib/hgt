import GaloisForLFunctions.RHTower.XiTwoPortProducerLinePeel

/-!
# The defect transport law of the two-port producer

For `h > 0` let `c = ½ + h`, `d = 1 + 2h` and `B_h(s) = ξ(s) + ξ(s − 2h)`. Call a height `T`
*shadow-free* if `|T − γ| > |β − ½|` for every zero `ρ = β + iγ` of `ξ`.

**Theorem** (`twoPort_zeroCount_le`). Let `T₁ < T₂` be shadow-free heights with
`Re ξ(c + iT_j) ≠ 0`. Count zeros with multiplicity in the rectangle `[c, d] × [T₁, T₂]`. Then the
zeros of `B_h` with `Re s > c` number at most the zeros of `ξ` with `Re s ≥ c`, plus one.

The zeros of `B_h` off the line `Re s = c` are the non-real zeros of `cos(hD)Ξ`, in pairs
`s ↔ 2c − s̄`. So in every window between shadow-free heights, the defect of the PTR producer at
depth `h` is at most twice the number of zeros of `ζ` at depth `≥ h`, plus two. The error is `O(1)`:
nothing of size `log T` remains.

**Proof.**
* The zeros of `B_h` and `ξ` on the left edge are peeled off (`exists_line_peel_argument`).
* `B_h` is real on the line, so its cofactor has constant phase there and the left edge contributes
  nothing (`exists_lineReal_argument_identity`).
* The phase of the cofactor of `ξ` along the left edge crosses a level at every new real zero of
  `cos(hD)Ξ` (`exists_line_phase_levels`).
* On the other three edges `Re(B_h/ξ) > 0`: on the right edge by monotonicity of `|ξ|` beyond
  `Re s = 1`, on the horizontal edges by shadow-freeness. So the argument variations of `B_h` and
  `ξ` there differ by less than `π` each.
* On the line, `B_h` vanishes at least to the order of `ξ`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## Edge integrability -/

theorem intervalIntegrable_re_logDeriv_vertical {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (hne : ∀ t ∈ Icc T₁ T₂, f ((x : ℂ) + t * I) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (logDeriv f ((x : ℂ) + t * I)).re) volume T₁ T₂ := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hT]
  intro t ht
  have hc : ContinuousAt (fun u : ℝ => (x : ℂ) + u * I) t := by fun_prop
  exact (Complex.continuous_re.continuousAt.comp
    ((continuousAt_logDeriv_of_analyticAt (hf.analyticAt _) (hne t ht)).comp
      (f := fun u : ℝ => (x : ℂ) + u * I) hc)).continuousWithinAt

theorem intervalIntegrable_im_logDeriv_horizontal {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c d T : ℝ} (hcd : c ≤ d) (hne : ∀ x ∈ Icc c d, f ((x : ℂ) + T * I) ≠ 0) :
    IntervalIntegrable (fun x : ℝ => (logDeriv f ((x : ℂ) + T * I)).im) volume c d := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hcd]
  intro x hx
  have hc : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) x := by fun_prop
  exact (Complex.continuous_im.continuousAt.comp
    ((continuousAt_logDeriv_of_analyticAt (hf.analyticAt _) (hne x hx)).comp
      (f := fun u : ℝ => (u : ℂ) + T * I) hc)).continuousWithinAt

/-! ## Peeling the left edge -/

/-- **The peeled argument principle.** The zeros of `F` on the left edge are divided out; the
cofactor's argument variation along the left edge equals the three other edges of `F`, minus `π`
per left-edge zero and `2π` per interior zero. -/
theorem exists_line_peel_argument {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hne : ∃ z, F z ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ Icc c d, F ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ Icc c d, F ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ Icc T₁ T₂, F ((d : ℂ) + t * I) ≠ 0) :
    ∃ S : Finset ℂ, (∀ w, w ∈ S ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ w.re = c)) ∧
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ z, F z = linePoly S (fun w => (analyticOrderAt F w).toNat) z * G z) ∧
      (∀ t ∈ Icc T₁ T₂, G ((c : ℂ) + t * I) ≠ 0) ∧
    ∃ Z : Finset ℂ, (∀ w, w ∈ Z ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ c < w.re)) ∧
      (∫ t in T₁..T₂, (logDeriv G ((c : ℂ) + t * I)).re)
        = ((∫ t in T₁..T₂, (logDeriv F ((d : ℂ) + t * I)).re)
          + (∫ x in c..d, (logDeriv F ((x : ℂ) + T₁ * I)).im)
          - (∫ x in c..d, (logDeriv F ((x : ℂ) + T₂ * I)).im))
          - Real.pi * ∑ w ∈ S, ((analyticOrderAt F w).toNat : ℝ)
          - 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt F w).toNat : ℝ) := by
  classical
  have hFan : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  have hcd' : c ≤ d := hcd.le
  have hT' : T₁ ≤ T₂ := hT.le
  have hrect : ∀ z : ℂ, z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ↔ z ∈ (Icc c d ×ℂ Icc T₁ T₂) := by
    intro z; rw [uIcc_of_le hcd', uIcc_of_le hT']
  have hfinR := entire_zeros_closedRectangle_finite hFan hne ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I)
  set S : Finset ℂ := hfinR.toFinset.filter (fun w => w.re = c) with hSdef
  have hSmem : ∀ w, w ∈ S ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ w.re = c) := by
    intro w
    rw [hSdef, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    rw [uIcc_of_le hcd', uIcc_of_le hT']
    tauto
  -- left-edge zeros sit strictly between the heights
  have hSstrict : ∀ w ∈ S, w.re = c ∧ T₁ < w.im ∧ w.im < T₂ := by
    intro w hw
    obtain ⟨hwR, hw0, hwc⟩ := (hSmem w).mp hw
    rw [mem_reProdIm] at hwR
    refine ⟨hwc, lt_of_le_of_ne hwR.2.1 ?_, lt_of_le_of_ne hwR.2.2 ?_⟩
    · intro h0
      apply hbot w.re (by rw [hwc]; exact ⟨le_rfl, hcd'⟩)
      have : (w.re : ℂ) + T₁ * I = w := by apply Complex.ext <;> simp [h0]
      rw [this]; exact hw0
    · intro h0
      apply htop w.re (by rw [hwc]; exact ⟨le_rfl, hcd'⟩)
      have : (w.re : ℂ) + T₂ * I = w := by apply Complex.ext <;> simp [h0]
      rw [this]; exact hw0
  obtain ⟨m, G, hGan, hm, hG0, hfac0⟩ := exists_finite_peel isOpen_univ hFan S (by simp)
    (fun w _ => analyticOrderAt_ne_top_of_entire_exists_ne_zero hFan hne w)
  set mF : ℂ → ℕ := fun w => (analyticOrderAt F w).toNat with hmF
  have hfac : ∀ z, F z = linePoly S mF z * G z := by
    intro z
    rw [hfac0 z (mem_univ z)]
    congr 1
    unfold linePoly
    exact Finset.prod_congr rfl fun w hw => by rw [hm w hw]
  have hGd : Differentiable ℂ G := fun z => (hGan z (mem_univ z)).differentiableAt
  have hG_of_F : ∀ z, F z ≠ 0 → G z ≠ 0 := by
    intro z hz h0; apply hz; rw [hfac z, h0, mul_zero]
  have hGleft : ∀ t ∈ Icc T₁ T₂, G ((c : ℂ) + t * I) ≠ 0 := by
    intro t ht
    by_cases hz : F ((c : ℂ) + t * I) = 0
    · apply hG0
      rw [hSmem]
      refine ⟨?_, hz, by simp⟩
      rw [mem_reProdIm]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add]
      exact ⟨⟨le_rfl, hcd'⟩, ht⟩
    · exact hG_of_F _ hz
  refine ⟨S, hSmem, G, hGd, hfac, hGleft, ?_⟩
  -- the argument principle for the cofactor
  have hGne : ∃ z, G z ≠ 0 := ⟨_, hG_of_F _ (hright T₁ ⟨le_rfl, hT'⟩)⟩
  obtain ⟨Z, hZ, hid⟩ := exists_entire_argument_variation_rectangle hGan hGne hcd hT
    (fun x hx => hG_of_F _ (hbot x (by rwa [uIcc_of_le hcd'] at hx)))
    (fun x hx => hG_of_F _ (htop x (by rwa [uIcc_of_le hcd'] at hx)))
    (fun t ht => hG_of_F _ (hright t (by rwa [uIcc_of_le hT'] at ht)))
    (fun t ht => hGleft t (by rwa [uIcc_of_le hT'] at ht))
  -- zeros of the cofactor are the zeros of `F` right of the edge, with the same orders
  have hPne : ∀ z, c < z.re → linePoly S mF z ≠ 0 := by
    intro z hz
    refine linePoly_ne_zero fun w hw h0 => ?_
    rw [h0, (hSstrict w hw).1] at hz; exact lt_irrefl _ hz
  have hZmem : ∀ w, w ∈ Z ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ c < w.re) := by
    intro w
    rw [hZ, hrect]
    constructor
    · rintro ⟨hwR, hw0⟩
      have hF0 : F w = 0 := by rw [hfac, hw0, mul_zero]
      refine ⟨hwR, hF0, lt_of_le_of_ne (mem_reProdIm.mp hwR).1.1 fun h0 => ?_⟩
      exact hG0 w ((hSmem w).mpr ⟨hwR, hF0, h0.symm⟩) hw0
    · rintro ⟨hwR, hF0, hwc⟩
      refine ⟨hwR, ?_⟩
      rw [hfac] at hF0
      exact (mul_eq_zero.mp hF0).resolve_left (hPne w hwc)
  have hord : ∀ w ∈ Z, analyticOrderAt G w = analyticOrderAt F w := by
    intro w hw
    have hwc := ((hZmem w).mp hw).2.2
    have hPan : AnalyticAt ℂ (linePoly S mF) w := (differentiable_linePoly S mF).analyticAt w
    have hFeq : F = linePoly S mF * G := funext hfac
    rw [hFeq, analyticOrderAt_mul hPan (hGan w (mem_univ w)),
      (hPan.analyticOrderAt_eq_zero).mpr (hPne w hwc), zero_add]
  -- the edges of `F` split into those of the polynomial and of the cofactor
  have hPedge : ∀ z, (∀ w ∈ S, z ≠ w) → G z ≠ 0 →
      logDeriv F z = logDeriv (linePoly S mF) z + logDeriv G z := by
    intro z hz hGz
    have hFeq : F = fun z => linePoly S mF z * G z := funext hfac
    rw [hFeq]
    exact logDeriv_mul z (linePoly_ne_zero hz) hGz (differentiable_linePoly S mF z) (hGd z)
  have hRne : ∀ t : ℝ, ∀ w ∈ S, (d : ℂ) + t * I ≠ w := by
    intro t w hw h0
    have := congrArg Complex.re h0; simp [(hSstrict w hw).1] at this; linarith
  have hBne : ∀ x : ℝ, ∀ w ∈ S, (x : ℂ) + T₁ * I ≠ w := by
    intro x w hw h0
    have := congrArg Complex.im h0; simp at this; linarith [(hSstrict w hw).2.1]
  have hTne : ∀ x : ℝ, ∀ w ∈ S, (x : ℂ) + T₂ * I ≠ w := by
    intro x w hw h0
    have := congrArg Complex.im h0; simp at this; linarith [(hSstrict w hw).2.2]
  have hGR : ∀ t ∈ Icc T₁ T₂, G ((d : ℂ) + t * I) ≠ 0 := fun t ht => hG_of_F _ (hright t ht)
  have hGB : ∀ x ∈ Icc c d, G ((x : ℂ) + T₁ * I) ≠ 0 := fun x hx => hG_of_F _ (hbot x hx)
  have hGT : ∀ x ∈ Icc c d, G ((x : ℂ) + T₂ * I) ≠ 0 := fun x hx => hG_of_F _ (htop x hx)
  have hPR : ∀ t ∈ Icc T₁ T₂, linePoly S mF ((d : ℂ) + t * I) ≠ 0 :=
    fun t _ => linePoly_ne_zero (hRne t)
  have hPB : ∀ x ∈ Icc c d, linePoly S mF ((x : ℂ) + T₁ * I) ≠ 0 :=
    fun x _ => linePoly_ne_zero (hBne x)
  have hPT : ∀ x ∈ Icc c d, linePoly S mF ((x : ℂ) + T₂ * I) ≠ 0 :=
    fun x _ => linePoly_ne_zero (hTne x)
  have eR : (∫ t in T₁..T₂, (logDeriv F ((d : ℂ) + t * I)).re) =
      (∫ t in T₁..T₂, (logDeriv (linePoly S mF) ((d : ℂ) + t * I)).re) +
        (∫ t in T₁..T₂, (logDeriv G ((d : ℂ) + t * I)).re) := by
    rw [← intervalIntegral.integral_add
      (intervalIntegrable_re_logDeriv_vertical (differentiable_linePoly S mF) hT' hPR)
      (intervalIntegrable_re_logDeriv_vertical hGd hT' hGR)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hT'] at ht
    rw [hPedge _ (hRne t) (hGR t ht), Complex.add_re]
  have eB : (∫ x in c..d, (logDeriv F ((x : ℂ) + T₁ * I)).im) =
      (∫ x in c..d, (logDeriv (linePoly S mF) ((x : ℂ) + T₁ * I)).im) +
        (∫ x in c..d, (logDeriv G ((x : ℂ) + T₁ * I)).im) := by
    rw [← intervalIntegral.integral_add
      (intervalIntegrable_im_logDeriv_horizontal (differentiable_linePoly S mF) hcd' hPB)
      (intervalIntegrable_im_logDeriv_horizontal hGd hcd' hGB)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hcd'] at hx
    rw [hPedge _ (hBne x) (hGB x hx), Complex.add_im]
  have eT : (∫ x in c..d, (logDeriv F ((x : ℂ) + T₂ * I)).im) =
      (∫ x in c..d, (logDeriv (linePoly S mF) ((x : ℂ) + T₂ * I)).im) +
        (∫ x in c..d, (logDeriv G ((x : ℂ) + T₂ * I)).im) := by
    rw [← intervalIntegral.integral_add
      (intervalIntegrable_im_logDeriv_horizontal (differentiable_linePoly S mF) hcd' hPT)
      (intervalIntegrable_im_logDeriv_horizontal hGd hcd' hGT)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hcd'] at hx
    rw [hPedge _ (hTne x) (hGT x hx), Complex.add_im]
  have hpoly := three_edge_linePoly hcd S mF hSstrict
  have hsumZ : ∑ w ∈ Z, ((analyticOrderAt G w).toNat : ℝ) =
      ∑ w ∈ Z, ((analyticOrderAt F w).toNat : ℝ) :=
    Finset.sum_congr rfl fun w hw => by rw [hord w hw]
  refine ⟨Z, hZmem, ?_⟩
  rw [hid, eR, eB, eT, hsumZ]
  simp only [hmF] at hpoly
  linarith

/-- **Line-real argument principle.** If `F` is real on the left edge, the three other edges
carry exactly `π` per left-edge zero and `2π` per interior zero. -/
theorem exists_lineReal_argument_identity {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hne : ∃ z, F z ≠ 0) {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hreal : ∀ t : ℝ, (F ((c : ℂ) + t * I)).im = 0)
    (hbot : ∀ x ∈ Icc c d, F ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ Icc c d, F ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ Icc T₁ T₂, F ((d : ℂ) + t * I) ≠ 0) :
    ∃ S : Finset ℂ, (∀ w, w ∈ S ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ w.re = c)) ∧
    ∃ Z : Finset ℂ, (∀ w, w ∈ Z ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ c < w.re)) ∧
      (∫ t in T₁..T₂, (logDeriv F ((d : ℂ) + t * I)).re)
          + (∫ x in c..d, (logDeriv F ((x : ℂ) + T₁ * I)).im)
          - (∫ x in c..d, (logDeriv F ((x : ℂ) + T₂ * I)).im)
        = Real.pi * ∑ w ∈ S, ((analyticOrderAt F w).toNat : ℝ)
          + 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt F w).toNat : ℝ) := by
  obtain ⟨S, hS, G, hGd, hfac, hGl, Z, hZ, hid⟩ :=
    exists_line_peel_argument hF hne hcd hT hbot htop hright
  have hleft0 : (∫ t in T₁..T₂, (logDeriv G ((c : ℂ) + t * I)).re) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    exact re_logDeriv_eq_zero_of_line_real hGd hreal (fun w hw => ((hS w).mp hw).2.2) hfac
      (hGl t ht)
  refine ⟨S, hS, Z, hZ, by linarith⟩

/-- **Level crossings on the left edge.** The phase of the peeled cofactor of `F` along the left
edge advances by the three other edges minus `π` per left-edge zero and `2π` per interior zero.
Each half-turn of it produces a zero of `Re F` on the edge. -/
theorem exists_line_phase_levels {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hne : ∃ z, F z ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ Icc c d, F ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ Icc c d, F ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ Icc T₁ T₂, F ((d : ℂ) + t * I) ≠ 0)
    (h₁ : (F ((c : ℂ) + T₁ * I)).re ≠ 0) (h₂ : (F ((c : ℂ) + T₂ * I)).re ≠ 0) :
    ∃ S : Finset ℂ, (∀ w, w ∈ S ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ w.re = c)) ∧
    ∃ Z : Finset ℂ, (∀ w, w ∈ Z ↔ (w ∈ (Icc c d ×ℂ Icc T₁ T₂) ∧ F w = 0 ∧ c < w.re)) ∧
    ∃ Λ : Finset ℝ, (∀ t ∈ Λ, t ∈ Ioo T₁ T₂ ∧ (F ((c : ℂ) + t * I)).re = 0) ∧
      (((∫ t in T₁..T₂, (logDeriv F ((d : ℂ) + t * I)).re)
          + (∫ x in c..d, (logDeriv F ((x : ℂ) + T₁ * I)).im)
          - (∫ x in c..d, (logDeriv F ((x : ℂ) + T₂ * I)).im))
        - Real.pi * ∑ w ∈ S, ((analyticOrderAt F w).toNat : ℝ)
        - 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt F w).toNat : ℝ)) / Real.pi - 1
        ≤ (Λ.card : ℝ) := by
  classical
  obtain ⟨S, hS, G, hGd, hfac, hGl, Z, hZ, hid⟩ :=
    exists_line_peel_argument hF hne hcd hT hbot htop hright
  have hT' : T₁ ≤ T₂ := hT.le
  set mF : ℂ → ℕ := fun w => (analyticOrderAt F w).toNat with hmF
  set κ : ℂ := I ^ (∑ w ∈ S, mF w) with hκ
  have hκ0 : κ ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  set γ : ℝ → ℂ := fun τ => κ * G ((c : ℂ) + τ * I) with hγ
  set γ' : ℝ → ℂ := fun τ => κ * (deriv G ((c : ℂ) + τ * I) * I) with hγ'
  have hpath : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (c : ℂ) + v * I) I u := by
    intro u; simpa using ((hasDerivAt_id u).ofReal_comp.mul_const I).const_add (c : ℂ)
  have hγd : ∀ τ : ℝ, HasDerivAt γ (γ' τ) τ := by
    intro τ
    exact ((hGd ((c : ℂ) + τ * I)).hasDerivAt.comp τ (hpath τ)).const_mul κ
  have hγne : ∀ τ ∈ Icc T₁ T₂, γ τ ≠ 0 := fun τ hτ => mul_ne_zero hκ0 (hGl τ hτ)
  have hGan : AnalyticOnNhd ℂ G univ := hGd.differentiableOn.analyticOnNhd isOpen_univ
  have hG'c : Continuous (deriv G) := by
    rw [← continuousOn_univ]; exact hGan.deriv.continuousOn
  have hγc : Continuous γ := continuous_const.mul (hGd.continuous.comp (by fun_prop))
  have hγ'c : Continuous γ' :=
    continuous_const.mul ((hG'c.comp (by fun_prop)).mul continuous_const)
  have hquot : ContinuousOn (fun τ => γ' τ / γ τ) (Icc T₁ T₂) :=
    hγ'c.continuousOn.div hγc.continuousOn hγne
  obtain ⟨L, hLc, hLd, hLexp⟩ :=
    exists_continuousOn_log_of_hasDerivAt hT' (fun τ _ => hγd τ) hquot hγne
  set ψ : ℝ → ℝ := fun τ => (L τ).im with hψ
  have hψc : ContinuousOn ψ (Icc T₁ T₂) := Complex.continuous_im.comp_continuousOn hLc
  -- the phase velocity is `Re(G'/G)` on the edge
  have hvel : ∀ τ ∈ Icc T₁ T₂, (γ' τ / γ τ).im = (logDeriv G ((c : ℂ) + τ * I)).re := by
    intro τ hτ
    have hG0 := hGl τ hτ
    have e : γ' τ / γ τ = I * logDeriv G ((c : ℂ) + τ * I) := by
      simp only [hγ, hγ', logDeriv_apply]
      field_simp
    rw [e]; simp [Complex.mul_im]
  have hadv : ψ T₂ - ψ T₁ = ∫ t in T₁..T₂, (logDeriv G ((c : ℂ) + t * I)).re := by
    have hψd : ∀ τ ∈ uIcc T₁ T₂, HasDerivAt ψ ((γ' τ / γ τ).im) τ := by
      intro τ hτ
      rw [uIcc_of_le hT'] at hτ
      exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ (hLd τ hτ)
    have hint : IntervalIntegrable (fun τ => (γ' τ / γ τ).im) volume T₁ T₂ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hT']
      exact Complex.continuous_im.comp_continuousOn hquot
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hψd hint]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le hT'] at hτ
    exact hvel τ hτ
  -- `Re F = p · Re γ` on the edge, with `p` real
  have hreF : ∀ t : ℝ, (F ((c : ℂ) + t * I)).re =
      (∏ w ∈ S, (t - w.im) ^ mF w) * (γ t).re := by
    intro t
    rw [hfac, linePoly_line mF (fun w hw => ((hS w).mp hw).2.2) t]
    simp only [hγ]
    rw [show I ^ (∑ w ∈ S, mF w) * ((∏ w ∈ S, (t - w.im) ^ mF w : ℝ) : ℂ) *
        G ((c : ℂ) + t * I) = ((∏ w ∈ S, (t - w.im) ^ mF w : ℝ) : ℂ) *
        (κ * G ((c : ℂ) + t * I)) by rw [hκ]; ring, Complex.re_ofReal_mul]
  have hcosγ : ∀ τ ∈ Icc T₁ T₂, (γ τ).re = Real.exp (L τ).re * Real.cos (ψ τ) := by
    intro τ hτ
    rw [hLexp τ hτ, Complex.exp_re]
  have hend : ∀ τ ∈ Icc T₁ T₂, (F ((c : ℂ) + τ * I)).re ≠ 0 → Real.cos (ψ τ) ≠ 0 := by
    intro τ hτ hF0 hcos
    apply hF0
    rw [hreF, hcosγ τ hτ, hcos, mul_zero, mul_zero]
  obtain ⟨Λ, hΛ, hcard⟩ := exists_level_finset hT' hψc (hend T₁ ⟨le_rfl, hT'⟩ h₁)
    (hend T₂ ⟨hT', le_rfl⟩ h₂)
  refine ⟨S, hS, Z, hZ, Λ, fun t ht => ⟨(hΛ t ht).1, ?_⟩, ?_⟩
  · have htI : t ∈ Icc T₁ T₂ := Ioo_subset_Icc_self (hΛ t ht).1
    rw [hreF, hcosγ t htI, (hΛ t ht).2, mul_zero, mul_zero]
  · rw [hadv, hid] at hcard
    exact hcard

/-! ## The transport law -/

/-- **Defect transport at shadow-free heights.** Let `h > 0`, `c = ½ + h`, `d = 1 + 2h`. Let
`T₁ < T₂` be heights outside every shadow `[γ − |β − ½|, γ + |β − ½|]` with
`Re ξ(c + iT_j) ≠ 0`. Then, with multiplicity in `[c, d] × [T₁, T₂]`,
`#{B_h = 0, Re s > c} ≤ #{ξ = 0, Re s ≥ c} + 1`. -/
theorem twoPort_zeroCount_le {h T₁ T₂ : ℝ} (hh : 0 < h) (hT : T₁ < T₂)
    (hg₁ : ∀ w, XiC w = 0 → w.im ^ 2 < (T₁ - w.re) ^ 2)
    (hg₂ : ∀ w, XiC w = 0 → w.im ^ 2 < (T₂ - w.re) ^ 2)
    (hA₁ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₁ * I)).re ≠ 0)
    (hA₂ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₂ * I)).re ≠ 0) :
    ∃ ZB Zξ : Finset ℂ,
      (∀ w, w ∈ ZB ↔ (w ∈ (Icc (1 / 2 + h) (1 + 2 * h) ×ℂ Icc T₁ T₂) ∧ twoPort h w = 0 ∧
        1 / 2 + h < w.re)) ∧
      (∀ w, w ∈ Zξ ↔ (w ∈ (Icc (1 / 2 + h) (1 + 2 * h) ×ℂ Icc T₁ T₂) ∧ xi w = 0 ∧
        1 / 2 + h ≤ w.re)) ∧
      ∑ w ∈ ZB, (analyticOrderAt (twoPort h) w).toNat ≤
        ∑ w ∈ Zξ, (analyticOrderAt xi w).toNat + 1 := by
  classical
  set c : ℝ := 1 / 2 + h with hc
  set d : ℝ := 1 + 2 * h with hd
  have hcd : c < d := by rw [hc, hd]; linarith
  have hT' : T₁ ≤ T₂ := hT.le
  set B := twoPort h with hBdef
  have hBd : Differentiable ℂ B := differentiable_twoPort h
  have hξd : Differentiable ℂ xi := xi_differentiable
  -- horizontal edges
  have hξH : ∀ {T : ℝ}, (∀ w, XiC w = 0 → w.im ^ 2 < (T - w.re) ^ 2) →
      ∀ x : ℝ, xi ((x : ℂ) + T * I) ≠ 0 := fun hg x => xi_ne_zero_of_shadowFree hg
  have hposH : ∀ {T : ℝ}, (∀ w, XiC w = 0 → w.im ^ 2 < (T - w.re) ^ 2) →
      (xi ((c : ℂ) + T * I)).re ≠ 0 →
      ∀ x ∈ Icc c d, 0 < (B ((x : ℂ) + T * I) / xi ((x : ℂ) + T * I)).re := by
    intro T hg hA x hx
    rcases eq_or_lt_of_le hx.1 with hxc | hxc
    · rw [← hxc]; exact re_twoPort_div_xi_line_pos hA
    · apply re_twoPort_div_xi_pos
      have e : (x : ℂ) + T * I - 2 * h = ((x - 2 * h : ℝ) : ℂ) + T * I := by push_cast; ring
      rw [e]
      exact normSq_xi_sub_lt_of_shadowFree hh hg hxc
  have hB_of_pos : ∀ z : ℂ, 0 < (B z / xi z).re → B z ≠ 0 := by
    intro z hz h0; rw [h0, zero_div] at hz; simp at hz
  -- right edge
  have hposR : ∀ t ∈ Icc T₁ T₂, 0 < (B ((d : ℂ) + t * I) / xi ((d : ℂ) + t * I)).re := by
    intro t _
    apply re_twoPort_div_xi_pos
    have e : (d : ℂ) + t * I - 2 * h = ((1 + 2 * h - 2 * h : ℝ) : ℂ) + t * I := by
      rw [hd]; push_cast; ring
    rw [e, hd]
    exact normSq_xi_one_lt hh t
  have hξR : ∀ t ∈ Icc T₁ T₂, xi ((d : ℂ) + t * I) ≠ 0 := fun t _ =>
    xi_ne_zero_of_one_le (by simp [hd]; linarith)
  have hBne : ∃ z, B z ≠ 0 := ⟨_, hB_of_pos _ (hposR T₁ ⟨le_rfl, hT'⟩)⟩
  have hξne : ∃ z, xi z ≠ 0 := ⟨_, hξR T₁ ⟨le_rfl, hT'⟩⟩
  -- the two argument identities
  obtain ⟨SB, hSB, ZB, hZB, idB⟩ := exists_lineReal_argument_identity hBd hBne hcd hT
    (fun t => twoPort_line_im h t)
    (fun x hx => hB_of_pos _ (hposH hg₁ hA₁ x hx))
    (fun x hx => hB_of_pos _ (hposH hg₂ hA₂ x hx))
    (fun t ht => hB_of_pos _ (hposR t ht))
  obtain ⟨Sξ, hSξ, Zξ', hZξ', Λ, hΛ, hcard⟩ := exists_line_phase_levels hξd hξne hcd hT
    (fun x _ => hξH hg₁ x) (fun x _ => hξH hg₂ x) hξR hA₁ hA₂
  -- edge comparisons
  have dR := abs_integral_re_logDeriv_sub_lt_pi (x := d) hT' hBd hξd hposR
  have dB := abs_integral_im_logDeriv_sub_lt_pi (T := T₁) hcd.le hBd hξd (hposH hg₁ hA₁)
  have dT := abs_integral_im_logDeriv_sub_lt_pi (T := T₂) hcd.le hBd hξd (hposH hg₂ hA₂)
  -- line zeros: `Sξ` and the level points lie in `SB`
  have hlineB : ∀ t : ℝ, (xi ((c : ℂ) + t * I)).re = 0 → B ((c : ℂ) + t * I) = 0 := by
    intro t ht
    simp only [hBdef]
    rw [twoPort_line, ht]; simp
  have hSξsub : Sξ ⊆ SB := by
    intro w hw
    obtain ⟨hwR, hw0, hwc⟩ := (hSξ w).mp hw
    have hwe : w = (c : ℂ) + w.im * I := by apply Complex.ext <;> simp [hwc]
    refine (hSB w).mpr ⟨hwR, ?_, hwc⟩
    rw [hwe]; apply hlineB; rw [← hwe, hw0]; simp
  set Λ' : Finset ℂ := Λ.image (fun t : ℝ => (c : ℂ) + t * I) with hΛ'
  have hinj : Set.InjOn (fun t : ℝ => (c : ℂ) + t * I) (Λ : Set ℝ) := by
    intro a _ b _ hab
    have := congrArg Complex.im hab; simpa using this
  have hΛ'card : Λ'.card = Λ.card := Finset.card_image_of_injOn hinj
  have hΛ'sub : Λ' ⊆ SB := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨htI, hre⟩ := hΛ t ht
    refine (hSB _).mpr ⟨?_, hlineB t hre, by simp⟩
    rw [mem_reProdIm]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    exact ⟨⟨le_rfl, hcd.le⟩, Ioo_subset_Icc_self htI⟩
  -- order comparison on the line
  have hBan : AnalyticOnNhd ℂ B univ := hBd.differentiableOn.analyticOnNhd isOpen_univ
  have hξan : AnalyticOnNhd ℂ xi univ := hξd.differentiableOn.analyticOnNhd isOpen_univ
  have hordB_ne : ∀ w, analyticOrderAt B w ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hBan hBne
  have hordξ_ne : ∀ w, analyticOrderAt xi w ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hξan hξne
  have hcmp : ∀ w ∈ Sξ, (analyticOrderAt xi w).toNat ≤ (analyticOrderAt B w).toNat := by
    intro w hw
    have hwc := ((hSξ w).mp hw).2.2
    have hwe : w = ((1 / 2 + h : ℝ) : ℂ) + w.im * I := by
      apply Complex.ext <;> simp [hwc, hc]
    have hn : ((analyticOrderAt xi w).toNat : ℕ∞) ≤ analyticOrderAt xi w :=
      ENat.coe_toNat_le_self _
    rw [hwe] at hn ⊢
    have := natCast_le_analyticOrderAt_twoPort hn
    rw [← hwe] at this ⊢
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hordB_ne w)
    rw [← hk] at this ⊢
    simp only [ENat.toNat_coe]
    exact_mod_cast this
  have hone_le : ∀ {f : ℂ → ℂ} {w : ℂ}, AnalyticAt ℂ f w → analyticOrderAt f w ≠ ⊤ → f w = 0 →
      1 ≤ (analyticOrderAt f w).toNat := by
    intro f w hf htop h0
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact (hf.analyticOrderAt_eq_zero.mp (by rw [← hk]; rfl)) h0
    rw [← hk, ENat.toNat_coe]; omega
  -- `MB ≥ Mξ + L − K`
  set MB : ℕ := ∑ w ∈ SB, (analyticOrderAt B w).toNat with hMB
  set Mξ : ℕ := ∑ w ∈ Sξ, (analyticOrderAt xi w).toNat with hMξ
  have hcountB : Mξ + (Λ.card - Sξ.card) ≤ MB := by
    have hdisj : Disjoint Sξ (Λ' \ Sξ) := Finset.disjoint_sdiff
    have hsub : Sξ ∪ (Λ' \ Sξ) ⊆ SB := Finset.union_subset hSξsub (Finset.sdiff_subset.trans hΛ'sub)
    have h1 : ∑ w ∈ Sξ ∪ (Λ' \ Sξ), (analyticOrderAt B w).toNat ≤ MB :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_union hdisj] at h1
    have h2 : Mξ ≤ ∑ w ∈ Sξ, (analyticOrderAt B w).toNat := Finset.sum_le_sum hcmp
    have h3 : (Λ' \ Sξ).card ≤ ∑ w ∈ Λ' \ Sξ, (analyticOrderAt B w).toNat := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun w hw => ?_
      have hwB := (Finset.mem_sdiff.mp hw).1
      exact hone_le (hBan w (mem_univ w)) (hordB_ne w) ((hSB w).mp (hΛ'sub hwB)).2.1
    have h4 : Λ'.card ≤ (Λ' \ Sξ).card + Sξ.card := Finset.card_le_card_sdiff_add_card
    rw [hΛ'card] at h4
    omega
  have hKle : Sξ.card ≤ Mξ := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun w hw => ?_
    exact hone_le (hξan w (mem_univ w)) (hordξ_ne w) ((hSξ w).mp hw).2.1
  -- the zero sets of the conclusion
  refine ⟨ZB, Zξ' ∪ Sξ, hZB, ?_, ?_⟩
  · intro w
    rw [Finset.mem_union, hZξ', hSξ]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, h2, h3.le⟩
      · exact ⟨h1, h2, h3.ge⟩
    · rintro ⟨h1, h2, h3⟩
      rcases eq_or_lt_of_le h3 with h3 | h3
      · exact Or.inr ⟨h1, h2, h3.symm⟩
      · exact Or.inl ⟨h1, h2, h3⟩
  · have hdisj : Disjoint Zξ' Sξ := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have := ((hZξ' w).mp h1).2.2
      rw [((hSξ w).mp h2).2.2] at this
      exact lt_irrefl _ this
    rw [Finset.sum_union hdisj]
    set NB : ℕ := ∑ w ∈ ZB, (analyticOrderAt B w).toNat with hNB
    set Nξ : ℕ := ∑ w ∈ Zξ', (analyticOrderAt xi w).toNat with hNξ
    -- real arithmetic
    have hπ : 0 < Real.pi := Real.pi_pos
    have idB' : ((∫ t in T₁..T₂, (logDeriv B ((d : ℂ) + t * I)).re)
        + (∫ x in c..d, (logDeriv B ((x : ℂ) + T₁ * I)).im)
        - (∫ x in c..d, (logDeriv B ((x : ℂ) + T₂ * I)).im))
        = Real.pi * (MB : ℝ) + 2 * Real.pi * (NB : ℝ) := by
      rw [idB, hMB, hNB]; push_cast; ring
    have hcard' : ((∫ t in T₁..T₂, (logDeriv xi ((d : ℂ) + t * I)).re)
        + (∫ x in c..d, (logDeriv xi ((x : ℂ) + T₁ * I)).im)
        - (∫ x in c..d, (logDeriv xi ((x : ℂ) + T₂ * I)).im))
        ≤ Real.pi * ((Λ.card : ℝ) + 1) + Real.pi * (Mξ : ℝ) + 2 * Real.pi * (Nξ : ℝ) := by
      have := hcard
      rw [div_sub_one hπ.ne', div_le_iff₀ hπ] at this
      rw [hMξ, hNξ]; push_cast
      linarith
    rw [abs_lt] at dR dB dT
    have hcountR : (Mξ : ℝ) + (Λ.card : ℝ) - (Sξ.card : ℝ) ≤ (MB : ℝ) := by
      have : (Mξ + (Λ.card - Sξ.card) : ℕ) ≤ MB := hcountB
      have h5 : ((Λ.card - Sξ.card : ℕ) : ℝ) ≥ (Λ.card : ℝ) - (Sξ.card : ℝ) := by
        rcases le_total Sξ.card Λ.card with hle | hle
        · rw [Nat.cast_sub hle]
        · rw [Nat.sub_eq_zero_of_le hle]; push_cast; linarith [(Nat.cast_le (α := ℝ)).mpr hle]
      have : ((Mξ + (Λ.card - Sξ.card) : ℕ) : ℝ) ≤ (MB : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have hKleR : (Sξ.card : ℝ) ≤ (Mξ : ℝ) := by exact_mod_cast hKle
    have hmain : 2 * (NB : ℝ) < 2 * ((Nξ : ℝ) + (Mξ : ℝ)) + 4 := by
      have h6 : 2 * Real.pi * (NB : ℝ) < 4 * Real.pi + 2 * Real.pi * (Nξ : ℝ) +
          Real.pi * (Sξ.card : ℝ) := by
        nlinarith [dR.1, dR.2, dB.1, dB.2, dT.1, dT.2]
      have h7 : 2 * Real.pi * (NB : ℝ) < Real.pi * (2 * ((Nξ : ℝ) + (Mξ : ℝ)) + 4) := by
        nlinarith
      exact lt_of_mul_lt_mul_left (by linarith : Real.pi * (2 * (NB : ℝ)) <
        Real.pi * (2 * ((Nξ : ℝ) + (Mξ : ℝ)) + 4)) hπ.le
    have : 2 * NB < 2 * (Nξ + Mξ) + 4 := by exact_mod_cast hmain
    omega

end

end RHTower
