import GaloisForLFunctions.HTGeometry.MeromorphicPrincipalPart
import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles

/-!
# The residue theorem on a rectangle, with poles of arbitrary order

The rectangle residue theorem available for simple poles extends to poles of any order: only the
order-one coefficient survives the boundary integral, because every higher inverse power
`(s - p)^{-m}`, `m ≥ 2`, has the single-valued primitive `(s - p)^{1-m}/(1-m)` on `ℂ \ {p}`, and the
four edges of the rectangle telescope to zero against a primitive.

* `rectangleIntegral_eq_zero_of_primitive` — the four-edge fundamental theorem of calculus.
* `rectangleIntegral_inv_pow_eq_zero` — the boundary integral of `(s - p)^{-m}` vanishes for
  `m ≥ 2`.
* `rectangleIntegral'_principalPart` — the boundary integral of a principal part is its
  order-one Laurent coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology Filter MeasureTheory intervalIntegral
open scoped Interval BigOperators

/-! ### The four-edge fundamental theorem of calculus -/

/-- A horizontal edge integral against a primitive. -/
theorem hIntegral_of_primitive {F G : ℂ → ℂ} {p : ℂ} {x₁ x₂ y : ℝ} (hy : y ≠ p.im)
    (hd : ∀ s : ℂ, s ≠ p → HasDerivAt F (G s) s) (hc : ContinuousOn G {p}ᶜ) :
    HIntegral G x₁ x₂ y = F (x₂ + y * I) - F (x₁ + y * I) := by
  have hne : ∀ x : ℝ, ((x : ℂ) + y * I) ≠ p := by
    intro x hx
    exact hy (by simpa using congrArg Complex.im hx)
  have hpath : ∀ x : ℝ, HasDerivAt (fun t : ℝ => ((t : ℂ) + y * I)) 1 x := by
    intro x
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * I)
  have hcomp : ∀ x ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun t : ℝ => F ((t : ℂ) + y * I)) (G ((x : ℂ) + y * I)) x := by
    intro x _
    have h := (hd _ (hne x)).scomp x (hpath x)
    rw [one_smul, Function.comp_def] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => G ((t : ℂ) + y * I)) (Set.uIcc x₁ x₂) := by
    refine hc.comp (by fun_prop) ?_
    intro x _
    exact hne x
  rw [HIntegral, integral_eq_sub_of_hasDerivAt hcomp hcont.intervalIntegrable]

/-- A vertical edge integral against a primitive. -/
theorem vIntegral_of_primitive {F G : ℂ → ℂ} {p : ℂ} {x y₁ y₂ : ℝ} (hx : x ≠ p.re)
    (hd : ∀ s : ℂ, s ≠ p → HasDerivAt F (G s) s) (hc : ContinuousOn G {p}ᶜ) :
    VIntegral G x y₁ y₂ = F (x + y₂ * I) - F (x + y₁ * I) := by
  have hne : ∀ y : ℝ, ((x : ℂ) + y * I) ≠ p := by
    intro y hy
    exact hx (by simpa using congrArg Complex.re hy)
  have hpath : ∀ y : ℝ, HasDerivAt (fun t : ℝ => ((x : ℂ) + t * I)) I y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ) * I)) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
    simpa using h1.const_add ((x : ℂ))
  have hcomp : ∀ y ∈ Set.uIcc y₁ y₂,
      HasDerivAt (fun t : ℝ => F ((x : ℂ) + t * I)) (I * G ((x : ℂ) + y * I)) y := by
    intro y _
    have h := (hd _ (hne y)).scomp y (hpath y)
    rw [smul_eq_mul, Function.comp_def] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => I * G ((x : ℂ) + t * I)) (Set.uIcc y₁ y₂) := by
    refine continuousOn_const.mul (hc.comp (by fun_prop) ?_)
    intro y _
    exact hne y
  have hI : VIntegral G x y₁ y₂ = ∫ t in y₁..y₂, I * G ((x : ℂ) + t * I) := by
    rw [VIntegral, smul_eq_mul, intervalIntegral.integral_const_mul]
  rw [hI, integral_eq_sub_of_hasDerivAt hcomp hcont.intervalIntegrable]

/-- **The four-edge fundamental theorem of calculus.**  A function with a single-valued primitive
off one point integrates to zero over any rectangle border avoiding that point. -/
theorem rectangleIntegral_eq_zero_of_primitive {F G : ℂ → ℂ} {z w p : ℂ}
    (hzre : z.re ≠ p.re) (hwre : w.re ≠ p.re) (hzim : z.im ≠ p.im) (hwim : w.im ≠ p.im)
    (hd : ∀ s : ℂ, s ≠ p → HasDerivAt F (G s) s) (hc : ContinuousOn G {p}ᶜ) :
    RectangleIntegral G z w = 0 := by
  rw [RectangleIntegral, hIntegral_of_primitive hzim hd hc, hIntegral_of_primitive hwim hd hc,
    vIntegral_of_primitive hwre hd hc, vIntegral_of_primitive hzre hd hc]
  ring

/-! ### Higher inverse powers integrate to zero -/

/-- The primitive of `(s - p)^{-m}` for `m ≥ 2`. -/
noncomputable def invPowPrimitive (p : ℂ) (m : ℕ) : ℂ → ℂ :=
  fun s => (s - p) ^ ((1 : ℤ) - (m : ℤ)) / (((1 : ℤ) - (m : ℤ) : ℤ) : ℂ)

theorem hasDerivAt_invPowPrimitive {p : ℂ} {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : s ≠ p) :
    HasDerivAt (invPowPrimitive p m) (((s - p) ^ m)⁻¹) s := by
  have hne : s - p ≠ 0 := sub_ne_zero.mpr hs
  have hnz : ((1 : ℤ) - (m : ℤ)) ≠ 0 := by omega
  have hden : ((((1 : ℤ) - (m : ℤ)) : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hnz
  have hbase := hasDerivAt_zpow ((1 : ℤ) - (m : ℤ)) (s - p) (Or.inl hne)
  have hshift : HasDerivAt (fun t : ℂ => t - p) 1 s := (hasDerivAt_id s).sub_const p
  have hcomp := hbase.comp s hshift
  rw [Function.comp_def, mul_one] at hcomp
  have hfinal := hcomp.div_const ((((1 : ℤ) - (m : ℤ)) : ℤ) : ℂ)
  refine hfinal.congr_deriv ?_
  have hexp : (1 : ℤ) - (m : ℤ) - 1 = -(m : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast]
  field_simp

/-- **The boundary integral of a higher inverse power vanishes.** -/
theorem rectangleIntegral_inv_pow_eq_zero {z w p : ℂ} {m : ℕ} (hm : 2 ≤ m)
    (hzre : z.re ≠ p.re) (hwre : w.re ≠ p.re) (hzim : z.im ≠ p.im) (hwim : w.im ≠ p.im) :
    RectangleIntegral (fun s => ((s - p) ^ m)⁻¹) z w = 0 := by
  refine rectangleIntegral_eq_zero_of_primitive (F := invPowPrimitive p m)
    hzre hwre hzim hwim (fun s hs => hasDerivAt_invPowPrimitive hm hs) ?_
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  have hne : s - p ≠ 0 := sub_ne_zero.mpr hs
  exact ((continuous_id.sub continuous_const).continuousAt.pow m).inv₀ (pow_ne_zero _ hne)


/-! ### The boundary integral of a principal part -/

/-- The part of a principal part of pole order at least two. -/
noncomputable def principalTail (f : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun s => ∑ j ∈ Finset.range n,
    laurentCoeff f a ((j : ℤ) - (n + 1)) * ((s - a) ^ (n + 1 - j))⁻¹

/-- Away from `a` the higher-order part is analytic. -/
theorem analyticAt_principalTail {f : ℂ → ℂ} {a : ℂ} (n : ℕ) {s : ℂ} (hs : s ≠ a) :
    AnalyticAt ℂ (principalTail f a n) s := by
  refine Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ?_
  refine AnalyticAt.inv ?_ (pow_ne_zero _ (sub_ne_zero.mpr hs))
  exact (analyticAt_id.sub analyticAt_const).pow _

/-- **The higher-order part of a principal part has vanishing boundary integral.** -/
theorem rectangleIntegral_principalTail_eq_zero {f : ℂ → ℂ} {a z w : ℂ} {n : ℕ}
    (hzre : z.re ≠ a.re) (hwre : w.re ≠ a.re) (hzim : z.im ≠ a.im) (hwim : w.im ≠ a.im) :
    RectangleIntegral (principalTail f a n) z w = 0 := by
  refine rectangleIntegral_eq_zero_of_primitive
    (F := fun s => ∑ j ∈ Finset.range n,
      laurentCoeff f a ((j : ℤ) - (n + 1)) * invPowPrimitive a (n + 1 - j) s)
    hzre hwre hzim hwim ?_ ?_
  · intro s hs
    refine HasDerivAt.fun_sum fun j hj => ?_
    have hjn : j < n := Finset.mem_range.mp hj
    have hm : 2 ≤ n + 1 - j := by omega
    exact (hasDerivAt_invPowPrimitive hm hs).const_mul _
  · exact fun s hs => (analyticAt_principalTail n hs).continuousAt.continuousWithinAt

/-- A principal part truncated at `n+1` splits as its order-one term plus the higher-order tail. -/
theorem principalPart_eq_tail_add_residue (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    principalPart f a (n + 1)
      = principalTail f a n + fun s => laurentCoeff f a (-1) / (s - a) := by
  funext s
  simp only [principalPart, principalTail, Pi.add_apply, Finset.sum_range_succ]
  push_cast
  have h1 : ((n : ℤ) - ((n : ℤ) + 1)) = -1 := by ring
  have h2 : n + 1 - n = 1 := by omega
  rw [h1, h2, pow_one, div_eq_mul_inv]

/-- **The boundary integral of a principal part is its order-one Laurent coefficient.** -/
theorem rectangleIntegral'_principalPart {f : ℂ → ℂ} {a z w : ℂ} {n : ℕ}
    (hz : z.re ≤ w.re) (hw : z.im ≤ w.im) (ha : Rectangle z w ∈ 𝓝 a) :
    RectangleIntegral' (principalPart f a (n + 1)) z w = laurentCoeff f a (-1) := by
  obtain ⟨hre, him⟩ := rectangle_mem_nhds_iff.mp ha
  have hzre : z.re ≠ a.re := (Set.ne_left_of_mem_uIoo hre).symm
  have hwre : w.re ≠ a.re := (Set.ne_right_of_mem_uIoo hre).symm
  have hzim : z.im ≠ a.im := (Set.ne_left_of_mem_uIoo him).symm
  have hwim : w.im ≠ a.im := (Set.ne_right_of_mem_uIoo him).symm
  have hdisj : Disjoint (RectangleBorder z w) {a} :=
    rectangleBorder_disjoint_singleton ⟨hzre.symm, hwre.symm, hzim.symm, hwim.symm⟩
  have hborder : ∀ s ∈ RectangleBorder z w, s ≠ a := fun s hs h =>
    Set.disjoint_left.mp hdisj hs (by simp [h])
  have hcontTail : ContinuousOn (principalTail f a n) (RectangleBorder z w) := fun s hs =>
    (analyticAt_principalTail n (hborder s hs)).continuousAt.continuousWithinAt
  have hcontRes : ContinuousOn (fun s => laurentCoeff f a (-1) / (s - a)) (RectangleBorder z w) := by
    intro s hs
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (by fun_prop) (sub_ne_zero.mpr (hborder s hs)))
  rw [principalPart_eq_tail_add_residue, RectangleIntegral',
    RectangleBorderIntegrable.add hcontTail.rectangleBorder_integrable
      hcontRes.rectangleBorder_integrable,
    rectangleIntegral_principalTail_eq_zero hzre hwre hzim hwim, zero_add]
  exact ResidueTheoremInRectangle hz hw ha

/-! ### Finite additivity of the boundary integral -/

/-- Border integrability is closed under finite sums. -/
theorem rectangleBorderIntegrable_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (h : ∀ i ∈ S, ContinuousOn (F i) (RectangleBorder z w)) :
    RectangleBorderIntegrable (fun s => ∑ i ∈ S, F i s) z w :=
  (continuousOn_finsetSum S h).rectangleBorder_integrable

/-- **The boundary integral is additive over finite sums.** -/
theorem rectangleIntegral_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (h : ∀ i ∈ S, ContinuousOn (F i) (RectangleBorder z w)) :
    RectangleIntegral (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, RectangleIntegral (F i) z w := by
  classical
  induction S using Finset.induction with
  | empty => simp [RectangleIntegral, HIntegral, VIntegral]
  | insert i S hi IH =>
      have hi' : ∀ j ∈ S, ContinuousOn (F j) (RectangleBorder z w) := fun j hj =>
        h j (Finset.mem_insert_of_mem hj)
      have hsplit : (fun s => ∑ j ∈ insert i S, F j s)
          = F i + fun s => ∑ j ∈ S, F j s := by
        funext s
        simp [Finset.sum_insert hi]
      rw [hsplit, RectangleBorderIntegrable.add
        (h i (Finset.mem_insert_self i S)).rectangleBorder_integrable
        (rectangleBorderIntegrable_finset_sum S F hi'), IH hi', Finset.sum_insert hi]

/-! ### The residue theorem -/

/-- **The residue theorem on a rectangle, for poles of arbitrary order.**  If `f` is analytic on
the closed rectangle away from a finite set `P` of interior points at which it is meromorphic, then
the normalized boundary integral is the sum of the order-one Laurent coefficients at those points.

The proof subtracts the principal parts: the difference extends analytically across every point of
`P`, hence has vanishing boundary integral, while each principal part contributes exactly its
order-one coefficient. -/
theorem rectangleIntegral'_eq_sum_laurentCoeff {f : ℂ → ℂ} {z w : ℂ} {P : Finset ℂ}
    (hz : z.re ≤ w.re) (hw : z.im ≤ w.im)
    (hP : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p)
    (hmero : ∀ p ∈ P, MeromorphicAt f p)
    (hoff : ∀ s ∈ Rectangle z w, s ∉ P → AnalyticAt ℂ f s) :
    RectangleIntegral' f z w = ∑ p ∈ P, laurentCoeff f p (-1) := by
  classical
  -- clearing exponents and analytic germs at the poles
  have key : ∀ p : ℂ, ∃ (m : ℕ) (g : ℂ → ℂ), p ∈ P →
      AnalyticAt ℂ g p ∧ ∀ s ≠ p, f s = g s + principalPart f p (m + 1) s := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨k, hk1, hk⟩ := exists_analyticAt_laurentShift_ge (hmero p hp) 1
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      obtain ⟨g, hg, hgeq⟩ := eq_add_principalPart hk
      exact ⟨m, g, fun _ => ⟨hg, hgeq⟩⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose m g hmg using key
  set PP : ℂ → ℂ → ℂ := fun p => principalPart f p (m p + 1) with hPP
  -- the corrected function and the analytic remainder
  set f₀ : ℂ → ℂ := fun s => if s ∈ P then g s s else f s with hf₀
  set Φ : ℂ → ℂ := fun s => f₀ s - ∑ p ∈ P, PP p s with hΦ
  -- geometry of the poles relative to the border
  have hcorner : ∀ p ∈ P, p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im := by
    intro p hp
    obtain ⟨hre, him⟩ := rectangle_mem_nhds_iff.mp (hP p hp)
    exact ⟨Set.ne_left_of_mem_uIoo hre, Set.ne_right_of_mem_uIoo hre,
      Set.ne_left_of_mem_uIoo him, Set.ne_right_of_mem_uIoo him⟩
  have hborder : ∀ s ∈ RectangleBorder z w, s ∉ P := by
    intro s hs hsP
    exact Set.disjoint_left.mp (rectangleBorder_disjoint_singleton (hcorner s hsP)) hs rfl
  -- `Φ` is analytic on the closed rectangle
  have hΦan : ∀ s ∈ Rectangle z w, AnalyticAt ℂ Φ s := by
    intro s hs
    by_cases hsP : s ∈ P
    · have hEq : Φ =ᶠ[𝓝 s] fun t => g s t - ∑ p ∈ P.erase s, PP p t := by
        have hopen : IsOpen (((P.erase s : Finset ℂ) : Set ℂ)ᶜ) :=
          ((P.erase s).finite_toSet.isClosed).isOpen_compl
        have hmem : (((P.erase s : Finset ℂ) : Set ℂ)ᶜ) ∈ 𝓝 s := by
          refine hopen.mem_nhds ?_
          simp
        filter_upwards [hmem] with t ht
        have htP : t ∉ P.erase s := fun hmem => ht (Finset.mem_coe.mpr hmem)
        have hsum : ∑ p ∈ P, PP p t = PP s t + ∑ p ∈ P.erase s, PP p t :=
          (Finset.add_sum_erase P (fun p => PP p t) hsP).symm
        by_cases hts : t = s
        · subst hts
          have h0 : PP t t = 0 := principalPart_self f t (m t + 1)
          simp only [hΦ, hf₀, if_pos hsP, hsum, h0]
          ring
        · have htnotP : t ∉ P := fun h => htP (Finset.mem_erase.mpr ⟨hts, h⟩)
          have hft : f t = g s t + PP s t := (hmg s hsP).2 t hts
          simp only [hΦ, hf₀, if_neg htnotP, hsum, hft]
          ring
      refine AnalyticAt.congr ?_ hEq.symm
      refine (hmg s hsP).1.sub (Finset.analyticAt_fun_sum _ fun p hp => ?_)
      exact analyticAt_principalPart _ (Finset.ne_of_mem_erase hp).symm
    · have hEq : Φ =ᶠ[𝓝 s] fun t => f t - ∑ p ∈ P, PP p t := by
        have hopen : IsOpen (((P : Finset ℂ) : Set ℂ)ᶜ) := (P.finite_toSet.isClosed).isOpen_compl
        have hmem : (((P : Finset ℂ) : Set ℂ)ᶜ) ∈ 𝓝 s := hopen.mem_nhds (by simpa using hsP)
        filter_upwards [hmem] with t ht
        have htP : t ∉ P := fun hmem' => ht (Finset.mem_coe.mpr hmem')
        simp only [hΦ, hf₀, if_neg htP]
      refine AnalyticAt.congr ?_ hEq.symm
      refine (hoff s hs hsP).sub (Finset.analyticAt_fun_sum _ fun p hp => ?_)
      have hne : s ≠ p := by rintro rfl; exact hsP hp
      exact analyticAt_principalPart _ hne
  -- each principal part is continuous on the border
  have hcontPP : ∀ p ∈ P, ContinuousOn (PP p) (RectangleBorder z w) := by
    intro p hp s hs
    have hne : s ≠ p := by rintro rfl; exact hborder s hs hp
    exact ((analyticAt_principalPart _ hne).continuousAt).continuousWithinAt
  have hcontΦ : ContinuousOn Φ (RectangleBorder z w) := by
    intro s hs
    exact (hΦan s (rectangleBorder_subset_rectangle z w hs)).continuousAt.continuousWithinAt
  -- decompose and integrate
  have hdecomp : f₀ = Φ + fun s => ∑ p ∈ P, PP p s := by
    funext s
    simp [hΦ]
  have hcongr : RectangleIntegral f z w = RectangleIntegral f₀ z w := by
    refine RectangleIntegral_congr ?_
    intro s hs
    simp only [hf₀, if_neg (hborder s hs)]
  have hzero : RectangleIntegral Φ z w = 0 :=
    HolomorphicOn.vanishesOnRectangle
      (fun s hs => ((hΦan s hs).differentiableAt).differentiableWithinAt) subset_rfl
  have hsplit : RectangleIntegral f₀ z w = ∑ p ∈ P, RectangleIntegral (PP p) z w := by
    rw [hdecomp, RectangleBorderIntegrable.add hcontΦ.rectangleBorder_integrable
      (rectangleBorderIntegrable_finset_sum P PP hcontPP), hzero, zero_add,
      rectangleIntegral_finset_sum P PP hcontPP]
  rw [RectangleIntegral', hcongr, hsplit, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact rectangleIntegral'_principalPart hz hw (hP p hp)

end GaloisForLFunctions.HTGeometry
