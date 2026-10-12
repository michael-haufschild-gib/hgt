import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount

/-!
# Nonreal roots of the shift average of a real polynomial

For a real polynomial `p` and `h ∈ ℝ` let `A(z) = (p(z + ih) + p(z − ih))/2 = cos(hD)p(z)`. This is
again a real polynomial, of the same degree (`shiftAvg`).

**Theorem** (`nonrealRootCount_shiftAvg_le`). `A` has at most `2·#{roots w of p : Im w > h}`
nonreal roots, counted with multiplicity. So the nonreal roots of `A` are at most the roots of `p`
at distance more than `h` from the real axis. If every root of `p` satisfies `|Im w| ≤ h`, then `A`
is real-rooted.

**Proof** (generalized Hermite–Biehler). Put `E(z) = p(z + ih)`; on the real line
`A(x) = Re E(x)`. The roots `w` with `Im w = h` give real linear factors of `E` and of `A`. For the
others, `E(x) = c·Π₀(x)·∏(x − ζ)` with `ζ = w − ih` not real, and
`∏(x − ζ) = M(x)e^{iθ(x)}`, `θ(x) = Σ arg(x − ζ)`, `M > 0`. The phase `θ` is continuous on `ℝ`; it
tends to `0` at `+∞` and to `π(#{Im ζ < 0} − #{Im ζ > 0})` at `−∞`. By the intermediate value
theorem `cos θ` vanishes at `#{Im ζ < 0} − #{Im ζ > 0}` distinct real points. Counting degrees gives
the bound.
-/

open Polynomial Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Real polynomials from conjugation-invariant complex polynomials -/

theorem exists_map_eq_of_map_conj {S : ℂ[X]} (hS : S.map (starRingEnd ℂ) = S) :
    ∃ R : ℝ[X], R.map Complex.ofRealHom = S := by
  have hl : S ∈ Polynomial.lifts Complex.ofRealHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h := congrArg (fun q : ℂ[X] => q.coeff n) hS
    simp only [coeff_map] at h
    refine ⟨(S.coeff n).re, ?_⟩
    have him : (S.coeff n).im = 0 := by
      have := Complex.conj_eq_iff_im.mp h
      exact this
    exact Complex.ext (by simp) (by simp [him])
  obtain ⟨R, hR⟩ := hl
  exact ⟨R, hR⟩

/-! ## The shift average -/

/-- `(p(z + ih) + p(z − ih))/2` as a complex polynomial. -/
def shiftAvgC (h : ℝ) (p : ℝ[X]) : ℂ[X] :=
  C (1 / 2 : ℂ) * ((p.map Complex.ofRealHom).comp (X + C ((h : ℂ) * I)) +
    (p.map Complex.ofRealHom).comp (X - C ((h : ℂ) * I)))

theorem map_conj_comp_add (h : ℝ) (p : ℝ[X]) :
    ((p.map Complex.ofRealHom).comp (X + C ((h : ℂ) * I))).map (starRingEnd ℂ) =
      (p.map Complex.ofRealHom).comp (X - C ((h : ℂ) * I)) := by
  rw [Polynomial.map_comp, Polynomial.map_map]
  have e : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext x; simp
  rw [e]
  congr 1
  simp [Polynomial.map_add, sub_eq_add_neg]

theorem map_conj_shiftAvgC (h : ℝ) (p : ℝ[X]) :
    (shiftAvgC h p).map (starRingEnd ℂ) = shiftAvgC h p := by
  have h2 : ((p.map Complex.ofRealHom).comp (X - C ((h : ℂ) * I))).map (starRingEnd ℂ) =
      (p.map Complex.ofRealHom).comp (X + C ((h : ℂ) * I)) := by
    rw [← map_conj_comp_add, Polynomial.map_map]
    have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext x; simp
    rw [this, Polynomial.map_id]
  unfold shiftAvgC
  rw [Polynomial.map_mul, Polynomial.map_add, map_conj_comp_add, h2, Polynomial.map_C]
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-- The shift average `(p(z + ih) + p(z − ih))/2` as a real polynomial. -/
def shiftAvg (h : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (exists_map_eq_of_map_conj (map_conj_shiftAvgC h p)).choose

theorem map_shiftAvg (h : ℝ) (p : ℝ[X]) :
    (shiftAvg h p).map Complex.ofRealHom = shiftAvgC h p :=
  (exists_map_eq_of_map_conj (map_conj_shiftAvgC h p)).choose_spec

theorem eval_map_shiftAvg (h : ℝ) (p : ℝ[X]) (z : ℂ) :
    ((shiftAvg h p).map Complex.ofRealHom).eval z =
      ((p.map Complex.ofRealHom).eval (z + h * I) + (p.map Complex.ofRealHom).eval (z - h * I)) / 2 := by
  rw [map_shiftAvg, shiftAvgC]
  simp only [eval_mul, eval_C, eval_add, eval_comp, eval_X, eval_sub]
  ring

/-! ## The phase of a product of nonreal linear factors -/

theorem sub_mem_slitPlane {ζ : ℂ} (hζ : ζ.im ≠ 0) (x : ℝ) : (x : ℂ) - ζ ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simpa using hζ

theorem continuous_arg_sub {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    Continuous fun x : ℝ => arg ((x : ℂ) - ζ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hc : Continuous fun y : ℝ => (y : ℂ) - ζ := Complex.continuous_ofReal.sub continuous_const
  exact (continuousAt_arg (sub_mem_slitPlane hζ x)).comp (f := fun y : ℝ => (y : ℂ) - ζ)
    hc.continuousAt

theorem tendsto_div_ofReal_atTop (ζ : ℂ) :
    Tendsto (fun x : ℝ => ζ / (x : ℂ)) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ‖ζ‖
  rw [mul_zero] at h
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (h.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, div_eq_mul_inv]

theorem tendsto_div_ofReal_atBot (ζ : ℂ) :
    Tendsto (fun x : ℝ => ζ / (x : ℂ)) atBot (𝓝 0) := by
  have h := (tendsto_div_ofReal_atTop (-ζ)).comp tendsto_neg_atBot_atTop
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, Complex.ofReal_neg, neg_div_neg_eq]

theorem tendsto_arg_sub_atTop (ζ : ℂ) : Tendsto (fun x : ℝ => arg ((x : ℂ) - ζ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (1 : ℂ) - ζ / x) atTop (𝓝 1) := by
    have := (tendsto_div_ofReal_atTop ζ).const_sub (1 : ℂ)
    simpa using this
  have h2 : Tendsto (fun x : ℝ => arg ((1 : ℂ) - ζ / x)) atTop (𝓝 0) := by
    rw [← arg_one]
    exact (continuousAt_arg (by simp [mem_slitPlane_iff])).tendsto.comp h1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [show (x : ℂ) - ζ = (x : ℂ) * (1 - ζ / x) by field_simp, arg_real_mul _ hx]

theorem tendsto_arg_sub_atBot_of_im_neg {ζ : ℂ} (hζ : ζ.im < 0) :
    Tendsto (fun x : ℝ => arg ((x : ℂ) - ζ)) atBot (𝓝 Real.pi) := by
  have h1 : Tendsto (fun x : ℝ => (-1 : ℂ) + ζ / x) atBot (𝓝 (-1)) := by
    have := (tendsto_div_ofReal_atBot ζ).const_add (-1 : ℂ)
    simpa using this
  have h2 : Tendsto (fun x : ℝ => (-1 : ℂ) + ζ / x) atBot (𝓝[{z : ℂ | 0 ≤ z.im}] (-1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
    filter_upwards [eventually_lt_atBot 0] with x hx
    simp only [add_im, neg_im, one_im, neg_zero, zero_add]
    rw [show ζ / (x : ℂ) = ζ * ((x⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    have : x⁻¹ < 0 := inv_lt_zero.mpr hx
    nlinarith
  have h3 := (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (z := -1) (by norm_num)
    (by simp)).comp h2
  refine h3.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  simp only [Function.comp_apply]
  rw [show (x : ℂ) - ζ = ((-x : ℝ) : ℂ) * (-1 + ζ / x) by push_cast; field_simp; ring,
    arg_real_mul _ (by linarith)]

theorem tendsto_arg_sub_atBot_of_im_pos {ζ : ℂ} (hζ : 0 < ζ.im) :
    Tendsto (fun x : ℝ => arg ((x : ℂ) - ζ)) atBot (𝓝 (-Real.pi)) := by
  have h1 : Tendsto (fun x : ℝ => (-1 : ℂ) + ζ / x) atBot (𝓝 (-1)) := by
    have := (tendsto_div_ofReal_atBot ζ).const_add (-1 : ℂ)
    simpa using this
  have h2 : Tendsto (fun x : ℝ => (-1 : ℂ) + ζ / x) atBot (𝓝[{z : ℂ | z.im < 0}] (-1)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
    filter_upwards [eventually_lt_atBot 0] with x hx
    simp only [add_im, neg_im, one_im, neg_zero, zero_add]
    rw [show ζ / (x : ℂ) = ζ * ((x⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    have : x⁻¹ < 0 := inv_lt_zero.mpr hx
    nlinarith
  have h3 := (tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := -1) (by norm_num)
    (by simp)).comp h2
  refine h3.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  simp only [Function.comp_apply]
  rw [show (x : ℂ) - ζ = ((-x : ℝ) : ℂ) * (-1 + ζ / x) by push_cast; field_simp; ring,
    arg_real_mul _ (by linarith)]

/-- The phase `θ(x) = Σ_ζ arg(x − ζ)`. -/
def phaseSum (Z : Multiset ℂ) (x : ℝ) : ℝ := (Z.map fun ζ => arg ((x : ℂ) - ζ)).sum

theorem continuous_phaseSum {Z : Multiset ℂ} (hZ : ∀ ζ ∈ Z, ζ.im ≠ 0) :
    Continuous (phaseSum Z) := by
  induction Z using Multiset.induction_on with
  | empty =>
    have e0 : phaseSum 0 = fun _ => 0 := by funext x; simp [phaseSum]
    rw [e0]; exact continuous_const
  | cons a Z ih =>
    have ha : a.im ≠ 0 := hZ a (Multiset.mem_cons_self a Z)
    have hZ' : ∀ ζ ∈ Z, ζ.im ≠ 0 := fun ζ hζ => hZ ζ (Multiset.mem_cons_of_mem hζ)
    have e : phaseSum (a ::ₘ Z) = fun x : ℝ => arg ((x : ℂ) - a) + phaseSum Z x := by
      funext x; simp [phaseSum]
    rw [e]
    exact (continuous_arg_sub ha).add (ih hZ')

theorem tendsto_phaseSum_atTop (Z : Multiset ℂ) : Tendsto (phaseSum Z) atTop (𝓝 0) := by
  induction Z using Multiset.induction_on with
  | empty =>
    have e0 : phaseSum 0 = fun _ => 0 := by funext x; simp [phaseSum]
    rw [e0]; exact tendsto_const_nhds
  | cons a Z ih =>
    have e : phaseSum (a ::ₘ Z) = fun x : ℝ => arg ((x : ℂ) - a) + phaseSum Z x := by
      funext x; simp [phaseSum]
    rw [e]
    simpa using (tendsto_arg_sub_atTop a).add ih

theorem tendsto_phaseSum_atBot {Z : Multiset ℂ} (hZ : ∀ ζ ∈ Z, ζ.im ≠ 0) :
    Tendsto (phaseSum Z) atBot (𝓝 (Real.pi * ((Multiset.card (Z.filter (fun ζ => ζ.im < 0)) : ℝ) -
      (Multiset.card (Z.filter (fun ζ => 0 < ζ.im)) : ℝ)))) := by
  induction Z using Multiset.induction_on with
  | empty =>
    have e0 : phaseSum 0 = fun _ => 0 := by funext x; simp [phaseSum]
    rw [e0]; simp
  | cons a Z ih =>
    have ha : a.im ≠ 0 := hZ a (Multiset.mem_cons_self a Z)
    have hZ' : ∀ ζ ∈ Z, ζ.im ≠ 0 := fun ζ hζ => hZ ζ (Multiset.mem_cons_of_mem hζ)
    have e : phaseSum (a ::ₘ Z) = fun x : ℝ => arg ((x : ℂ) - a) + phaseSum Z x := by
      funext x; simp [phaseSum]
    rw [e]
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have := (tendsto_arg_sub_atBot_of_im_neg hneg).add (ih hZ')
      convert this using 2
      rw [Multiset.filter_cons_of_pos (p := fun ζ : ℂ => ζ.im < 0) Z hneg,
        Multiset.filter_cons_of_neg (p := fun ζ : ℂ => 0 < ζ.im) Z (not_lt.mpr hneg.le)]
      simp only [Multiset.card_cons]
      push_cast
      ring
    · have := (tendsto_arg_sub_atBot_of_im_pos hpos).add (ih hZ')
      convert this using 2
      rw [Multiset.filter_cons_of_neg (p := fun ζ : ℂ => ζ.im < 0) Z (not_lt.mpr hpos.le),
        Multiset.filter_cons_of_pos (p := fun ζ : ℂ => 0 < ζ.im) Z hpos]
      simp only [Multiset.card_cons]
      push_cast
      ring

/-- Polar form of a product of linear factors at a real point. -/
theorem prod_sub_eq_polar (Z : Multiset ℂ) (x : ℝ) :
    (Z.map fun ζ => (x : ℂ) - ζ).prod =
      (((Z.map fun ζ => ‖(x : ℂ) - ζ‖).prod : ℝ) : ℂ) * Complex.exp ((phaseSum Z x : ℂ) * I) := by
  induction Z using Multiset.induction_on with
  | empty => simp [phaseSum]
  | cons a Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, phaseSum, Multiset.sum_cons]
    rw [ih]
    simp only [phaseSum]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ((x : ℂ) - a)]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring

theorem re_prod_sub_eq (Z : Multiset ℂ) (x : ℝ) :
    ((Z.map fun ζ => (x : ℂ) - ζ).prod).re =
      (Z.map fun ζ => ‖(x : ℂ) - ζ‖).prod * Real.cos (phaseSum Z x) := by
  rw [prod_sub_eq_polar, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-! ## Counting real roots through the phase -/

/-- **Generalized Hermite–Biehler count.** If a real polynomial `S` agrees on `ℝ` with
`c·Re ∏(x − ζ)` for nonreal `ζ`, then `S` has at least `#{Im ζ < 0} − #{Im ζ > 0}` distinct real
roots. -/
theorem card_roots_ge_of_eval_eq_re_prod {Z : Multiset ℂ} (hZ : ∀ ζ ∈ Z, ζ.im ≠ 0) {S : ℝ[X]}
    (hS0 : S ≠ 0) {c : ℝ} (hSx : ∀ x : ℝ, S.eval x = c * ((Z.map fun ζ => (x : ℂ) - ζ).prod).re) :
    Multiset.card (Z.filter (fun ζ => ζ.im < 0)) - Multiset.card (Z.filter (fun ζ => 0 < ζ.im)) ≤
      Multiset.card S.roots := by
  classical
  set a := Multiset.card (Z.filter (fun ζ => ζ.im < 0)) with ha
  set b := Multiset.card (Z.filter (fun ζ => 0 < ζ.im)) with hb
  rcases Nat.eq_zero_or_pos (a - b) with hn | hn
  · rw [hn]; exact Nat.zero_le _
  set n := a - b with hndef
  have hab : b ≤ a := by omega
  have hnR : (n : ℝ) = (a : ℝ) - b := by rw [hndef, Nat.cast_sub hab]
  have htop := tendsto_phaseSum_atTop Z
  have hbot := tendsto_phaseSum_atBot hZ
  rw [← ha, ← hb, ← hnR] at hbot
  have hpi := Real.pi_pos
  obtain ⟨Xp, hXp⟩ := (htop.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < Real.pi / 2))).exists
  have hev : ∀ᶠ x in atBot, Real.pi * n - Real.pi / 2 < phaseSum Z x ∧ x ≤ Xp :=
    (hbot.eventually (lt_mem_nhds (by linarith))).and (eventually_le_atBot Xp)
  obtain ⟨Xm, hXm, hle⟩ := hev.exists
  have hcont := (continuous_phaseSum hZ).continuousOn (s := Icc Xm Xp)
  have hivt := intermediate_value_Icc' hle hcont
  set v : Fin n → ℝ := fun k => Real.pi / 2 + (k : ℕ) * Real.pi with hv
  have hvmem : ∀ k, v k ∈ Icc (phaseSum Z Xp) (phaseSum Z Xm) := by
    intro k
    have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.2
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
    constructor
    · simp only [hv]; nlinarith
    · simp only [hv]; nlinarith
  choose x hxmem hxv using fun k => hivt (hvmem k)
  have hroot : ∀ k, x k ∈ S.roots := by
    intro k
    rw [mem_roots hS0, IsRoot, hSx, re_prod_sub_eq]
    have : Real.cos (phaseSum Z (x k)) = 0 := by
      rw [hxv k, hv]
      simp only
      have h := Real.cos_add_int_mul_pi (Real.pi / 2) ((k : ℕ) : ℤ)
      push_cast at h
      rw [h, Real.cos_pi_div_two, mul_zero]
    rw [this, mul_zero, mul_zero]
  have hinj : Function.Injective x := by
    intro k l hkl
    have h := congrArg (phaseSum Z) hkl
    rw [hxv, hxv, hv] at h
    simp only at h
    have : ((k : ℕ) : ℝ) = (l : ℕ) := by
      have := mul_right_cancel₀ hpi.ne' (by linarith : ((k : ℕ) : ℝ) * Real.pi = (l : ℕ) * Real.pi)
      exact this
    exact Fin.ext (by exact_mod_cast this)
  calc n = (Finset.univ.image x).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ S.roots.toFinset.card :=
        Finset.card_le_card fun y hy => by
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
          exact Multiset.mem_toFinset.mpr (hroot k)
    _ ≤ Multiset.card S.roots := Multiset.toFinset_card_le _

/-! ## The bound for the shift average -/

theorem conj_comp_ofReal : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
  ext x; simp

/-- **Nonreal roots of `cos(hD)p`.** The shift average `(p(z + ih) + p(z − ih))/2` of a nonzero
real polynomial has at most `2·#{roots w of p with Im w > h}` nonreal roots. -/
theorem nonrealRootCount_shiftAvg_le {p : ℝ[X]} (hp : p ≠ 0) (h : ℝ) :
    nonrealRootCount (shiftAvg h p) ≤
      2 * Multiset.card ((p.map Complex.ofRealHom).roots.filter (fun w => h < w.im)) := by
  classical
  set P := p.map Complex.ofRealHom with hP
  set N := P.roots with hN
  set N₀ := N.filter (fun w => w.im = h) with hN₀
  set N₁ := N.filter (fun w => ¬ w.im = h) with hN₁def
  set c : ℂ := (h : ℂ) * I with hc
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  have hsplit : Multiset.card N = P.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits P)
  have hlead : P.leadingCoeff = (p.leadingCoeff : ℂ) := by
    rw [hP, leadingCoeff_map]; rfl
  have hfac : P = C (p.leadingCoeff : ℂ) * (N.map fun w => X - C w).prod := by
    rw [← hlead]; exact (C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit).symm
  -- the shifted polynomial `E(z) = p(z + ih)`
  set Z : Multiset ℂ := N₁.map (fun w => w - c) with hZ
  set r₀ : ℝ[X] := (N₀.map fun w => X - C w.re).prod with hr₀
  set F₁ : ℂ[X] := (Z.map fun ζ => X - C ζ).prod with hF₁
  have hcomp : ∀ w : ℂ, (X - C w).comp (X + C c) = X - C (w - c) := by
    intro w; simp only [sub_comp, X_comp, C_comp, map_sub]; ring
  have hE : P.comp (X + C c) = C (p.leadingCoeff : ℂ) * r₀.map Complex.ofRealHom * F₁ := by
    rw [hfac, mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
    have hsplitN : N = N₀ + N₁ := (Multiset.filter_add_not _ N).symm
    conv_lhs => rw [hsplitN]
    rw [Multiset.map_add, Multiset.prod_add, mul_assoc]
    congr 2
    · rw [hr₀, Polynomial.map_multiset_prod, Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun w hw => ?_)
      have him : w.im = h := (Multiset.mem_filter.mp hw).2
      simp only [Function.comp_apply, hcomp, Polynomial.map_sub, map_X, map_C]
      congr 2
      apply Complex.ext <;> simp [hc, him]
    · rw [hF₁, hZ, Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun w _ => ?_)
      simp only [Function.comp_apply, hcomp]
  have hconjE : (P.comp (X + C c)).map (starRingEnd ℂ) =
      C (p.leadingCoeff : ℂ) * r₀.map Complex.ofRealHom * F₁.map (starRingEnd ℂ) := by
    rw [hE, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      conj_comp_ofReal]
    simp
  -- the real factor `S₁`
  set T : ℂ[X] := C (1 / 2 : ℂ) * (F₁ + F₁.map (starRingEnd ℂ)) with hT
  have hTconj : T.map (starRingEnd ℂ) = T := by
    rw [hT, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_map, Polynomial.map_C]
    have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext x; simp
    rw [this, Polynomial.map_id]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  obtain ⟨S₁, hS₁⟩ := exists_map_eq_of_map_conj hTconj
  have hshift : shiftAvg h p = C p.leadingCoeff * r₀ * S₁ := by
    apply Polynomial.map_injective _ Complex.ofRealHom.injective
    rw [map_shiftAvg, Polynomial.map_mul, Polynomial.map_mul, hS₁, Polynomial.map_C]
    unfold shiftAvgC
    rw [← hP, show (X - C ((h : ℂ) * I)) = X - C c by rfl, show (X + C ((h : ℂ) * I)) = X + C c by rfl]
    have hG : P.comp (X - C c) = (P.comp (X + C c)).map (starRingEnd ℂ) := by
      rw [hP, map_conj_comp_add]
    rw [hG, hconjE, hE, hT]
    simp only [Complex.ofRealHom_eq_coe]
    ring
  -- `S₁` is `Re F₁` on the real line
  have hF₁monic : F₁.Monic := monic_multiset_prod_of_monic _ _ fun ζ _ => monic_X_sub_C ζ
  have hT0 : T ≠ 0 := by
    intro h0
    have hcoef := congrArg (fun q : ℂ[X] => q.coeff F₁.natDegree) h0
    simp only [hT, coeff_C_mul, coeff_add, coeff_map, coeff_zero] at hcoef
    rw [hF₁monic.coeff_natDegree, map_one] at hcoef
    norm_num at hcoef
  have hS₁0 : S₁ ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hS₁
    exact hT0 hS₁.symm
  have hZim : ∀ ζ ∈ Z, ζ.im ≠ 0 := by
    intro ζ hζ
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hζ
    have him : ¬ w.im = h := (Multiset.mem_filter.mp hw).2
    simp only [hc, sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    exact sub_ne_zero.mpr him
  have hS₁x : ∀ x : ℝ, S₁.eval x = 1 * ((Z.map fun ζ => (x : ℂ) - ζ).prod).re := by
    intro x
    have h2 : (S₁.map Complex.ofRealHom).eval (x : ℂ) = ((S₁.eval x : ℝ) : ℂ) := by
      rw [eval_map, show (x : ℂ) = Complex.ofRealHom x from rfl, Polynomial.eval₂_at_apply]
      rfl
    have hconjx : (F₁.map (starRingEnd ℂ)).eval (x : ℂ) = (starRingEnd ℂ) (F₁.eval (x : ℂ)) := by
      rw [eval_map]
      calc eval₂ (starRingEnd ℂ) (x : ℂ) F₁ = eval₂ (starRingEnd ℂ) ((starRingEnd ℂ) (x : ℂ)) F₁ := by
            rw [Complex.conj_ofReal]
        _ = (starRingEnd ℂ) (F₁.eval (x : ℂ)) := Polynomial.eval₂_at_apply _ _
    have h3 : T.eval (x : ℂ) = (((F₁.eval (x : ℂ)).re : ℝ) : ℂ) := by
      rw [hT, eval_mul, eval_C, eval_add, hconjx, Complex.add_conj]
      push_cast
      ring
    have h4 : F₁.eval (x : ℂ) = (Z.map fun ζ => (x : ℂ) - ζ).prod := by
      rw [hF₁, eval_multiset_prod, Multiset.map_map]
      simp
    have h5 := congrArg (fun q : ℂ[X] => q.eval (x : ℂ)) hS₁
    have h6 : ((S₁.eval x : ℝ) : ℂ) = (((Z.map fun ζ => (x : ℂ) - ζ).prod.re : ℝ) : ℂ) := by
      rw [← h2, ← h4, ← h3]
      exact h5
    rw [one_mul]
    exact_mod_cast h6
  have hcount := card_roots_ge_of_eval_eq_re_prod hZim hS₁0 hS₁x
  -- the counts
  have hshift0 : shiftAvg h p ≠ 0 := by
    rw [hshift]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hS₁0
    · exact C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)
    · exact (monic_multiset_prod_of_monic _ _ fun w _ => monic_X_sub_C _).ne_zero
  have hroots : Multiset.card (shiftAvg h p).roots = Multiset.card N₀ + Multiset.card S₁.roots := by
    have e : (N₀.map fun w => X - C w.re) = (N₀.map Complex.re).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hshift, roots_mul (hshift ▸ hshift0), roots_C_mul _ (leadingCoeff_ne_zero.mpr hp), hr₀, e,
      roots_multiset_prod_X_sub_C, Multiset.card_add, Multiset.card_map]
  have hdeg : (shiftAvg h p).natDegree ≤ Multiset.card N := by
    have h1 : (shiftAvgC h p).natDegree ≤ P.natDegree := by
      unfold shiftAvgC
      refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le ?_ ?_))
      · rw [← hP, natDegree_comp, natDegree_X_add_C, mul_one]
      · rw [← hP, natDegree_comp]
        have : (X - C ((h : ℂ) * I)).natDegree = 1 := natDegree_X_sub_C _
        rw [this, mul_one]
    rw [← map_shiftAvg, natDegree_map] at h1
    rw [hsplit]; exact h1
  have hN : Multiset.card N = Multiset.card N₀ + Multiset.card N₁ := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  have himc : ∀ w : ℂ, (w - c).im = w.im - h := fun w => by simp [hc]
  have hN₁ : Multiset.card N₁ = Multiset.card (Z.filter (fun ζ => ζ.im < 0)) +
      Multiset.card (Z.filter (fun ζ => 0 < ζ.im)) := by
    have e1 : Multiset.card (Z.filter (fun ζ => ζ.im < 0)) =
        Multiset.card (N₁.filter (fun w => (w - c).im < 0)) := by
      rw [hZ, Multiset.filter_map, Multiset.card_map]; rfl
    have e2 : Multiset.card (Z.filter (fun ζ => 0 < ζ.im)) =
        Multiset.card (N₁.filter (fun w => ¬ (w - c).im < 0)) := by
      rw [hZ, Multiset.filter_map, Multiset.card_map]
      congr 1
      refine Multiset.filter_congr fun w hw => ?_
      have him : ¬ w.im = h := (Multiset.mem_filter.mp hw).2
      simp only [Function.comp_apply, himc]
      constructor
      · intro h1; linarith
      · intro h1; push Not at h1; exact lt_of_le_of_ne h1 (fun e => him (by linarith))
    rw [e1, e2, ← Multiset.card_add, Multiset.filter_add_not]
  have hpos : Multiset.card (Z.filter (fun ζ => 0 < ζ.im)) =
      Multiset.card (N.filter (fun w => h < w.im)) := by
    rw [hZ, Multiset.filter_map, Multiset.card_map, hN₁def, Multiset.filter_filter]
    congr 1
    refine Multiset.filter_congr fun w _ => ?_
    simp only [Function.comp_apply, himc]
    constructor
    · rintro ⟨h1, -⟩; linarith
    · intro h1; exact ⟨by linarith, fun e => by linarith⟩
  unfold nonrealRootCount
  rw [hroots]
  rw [← hpos]
  omega

end

end GaloisForLFunctions.HTGeometry
