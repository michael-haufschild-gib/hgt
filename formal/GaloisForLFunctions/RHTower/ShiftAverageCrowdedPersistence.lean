import GaloisForLFunctions.RHTower.XiCosineShiftDefectPersistence
import GaloisForLFunctions.HTGeometry.ShiftAverageNonrealCount

/-!
# Crowded persistence of a deep root under the shift average

For a real polynomial `p` and `h > 0` let `A = (p(z + ih) + p(z − ih))/2 = cos(hD)p`. Every nonreal
root of `A` comes from a root of `p` deeper than `h` (`nonrealRootCount_shiftAvg_le`). This file
proves a converse that holds in a crowded environment.

**Theorem** (`exists_zero_shiftAvg_near_deep_root`). Let `ζ₀` be a root of `p` with
`η + r < Im ζ₀ − h`. Write the remaining roots as `E + S`, where:
* every root in `S` satisfies `Im ζ ≤ η`;
* the roots in `E` change the modulus ratio across the shift by at most a factor `B` on the circle
  `|z − (ζ₀ − ih)| = r`.

Let `N` count the roots of `S` with `|Re ζ − Re ζ₀| ≤ H` and `Im ζ ≥ −η`, and put
`κ = 4h(Im ζ₀ − h − r − η)/((H + r)² + (Im ζ₀ + r + η)²)`. If
`((2h + r)/r)·B·(√(1 − κ))^N < 1`, then `A` has a root within distance `r` of `ζ₀ − ih`; it lies
above height `η`, so it is nonreal.

**Proof.** With `w± = z ± ih`, the product formula gives
`‖p(z − ih)‖/‖p(z + ih)‖ = Π_ζ ‖w₋ − ζ‖/‖w₊ − ζ‖`. The factors are:
* `ζ₀`: at most `(2h + r)/r`;
* a root below the circle: at most `1`, by `‖w₋ − ζ‖² = ‖w₊ − ζ‖² − 4h(Im z − Im ζ)`;
* a neighbour: at most `√(1 − κ)`.
So `‖p(z − ih)‖ < ‖p(z + ih)‖` on the circle, and Rouché against `p(· + ih)`, which vanishes at the
centre, gives the root of `A`.

A deep root therefore persists as a defect of `cos(hD)p` for every `h` below its depth minus the
margin `η + r`, as soon as enough shallow roots crowd around it. The two-point average absorbs
deep roots only in sparse configurations.
-/

open Polynomial Complex Metric

namespace RHTower.CrowdedPersistence

noncomputable section

theorem norm_multiset_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun x => ‖f x‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- The modulus of a complex polynomial through its roots. -/
theorem norm_eval_eq_prod (P : ℂ[X]) (w : ℂ) :
    ‖P.eval w‖ = ‖P.leadingCoeff‖ * (P.roots.map (fun ζ => ‖w - ζ‖)).prod := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := P))]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, norm_mul, norm_multiset_prod_map]
  simp

/-- The shift identity for one root: `‖z − ih − ζ‖² = ‖z + ih − ζ‖² − 4h(Im z − Im ζ)`. -/
theorem norm_sub_sq_shift (z ζ : ℂ) (h : ℝ) :
    ‖z - h * I - ζ‖ ^ 2 = ‖z + h * I - ζ‖ ^ 2 - 4 * h * (z.im - ζ.im) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp
  ring

/-- A root below the point does not increase the modulus across the shift. -/
theorem norm_sub_shift_le_of_im_le {z ζ : ℂ} {h : ℝ} (hh : 0 ≤ h) (hb : ζ.im ≤ z.im) :
    ‖z - h * I - ζ‖ ≤ ‖z + h * I - ζ‖ := by
  have e := norm_sub_sq_shift z ζ h
  have h4 : 0 ≤ 4 * h * (z.im - ζ.im) := by
    have : 0 ≤ z.im - ζ.im := by linarith
    positivity
  have hsq : ‖z - h * I - ζ‖ ^ 2 ≤ ‖z + h * I - ζ‖ ^ 2 := by linarith
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (z - h * I - ζ), norm_nonneg (z + h * I - ζ)]

/-- The crowding constant `κ = 4h(Im ζ₀ − h − r − η)/((H + r)² + (Im ζ₀ + r + η)²)`. -/
def crowdKappa (ζ₀ : ℂ) (h r η H : ℝ) : ℝ :=
  4 * h * (ζ₀.im - h - r - η) / ((H + r) ^ 2 + (ζ₀.im + r + η) ^ 2)

/-- **A neighbour contracts the modulus across the shift.** On the circle `|z − (ζ₀ − ih)| = r`, a
root `ζ` with `|Re ζ − Re ζ₀| ≤ H` and `|Im ζ| ≤ η` satisfies
`‖z − ih − ζ‖² ≤ (1 − κ)‖z + ih − ζ‖²`. -/
theorem norm_sub_shift_sq_le_of_neighbour {ζ₀ ζ z : ℂ} {h r η H : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (hη : 0 ≤ η) (hgap : η + r < ζ₀.im - h) (hz : ‖z - (ζ₀ - h * I)‖ = r)
    (hre : |ζ.re - ζ₀.re| ≤ H) (him₁ : -η ≤ ζ.im) (him₂ : ζ.im ≤ η) :
    ‖z - h * I - ζ‖ ^ 2 ≤ (1 - crowdKappa ζ₀ h r η H) * ‖z + h * I - ζ‖ ^ 2 := by
  have hx : |z.re - ζ₀.re| ≤ r := by
    have := Complex.abs_re_le_norm (z - (ζ₀ - h * I))
    simpa [hz] using this
  have hy : |z.im - (ζ₀.im - h)| ≤ r := by
    have := Complex.abs_im_le_norm (z - (ζ₀ - h * I))
    simpa [hz] using this
  rw [abs_le] at hx hy hre
  have hD : ‖z + h * I - ζ‖ ^ 2 = (z.re - ζ.re) ^ 2 + (z.im + h - ζ.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have e := norm_sub_sq_shift z ζ h
  set D := ‖z + h * I - ζ‖ ^ 2 with hDdef
  set M := (H + r) ^ 2 + (ζ₀.im + r + η) ^ 2 with hM
  have hMpos : 0 < M := by
    have : 0 < ζ₀.im + r + η := by linarith
    positivity
  have hDM : D ≤ M := by
    rw [hD]
    have h1 : (z.re - ζ.re) ^ 2 ≤ (H + r) ^ 2 := by
      have hab : |z.re - ζ.re| ≤ H + r := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (z.re - ζ.re), sq_abs (z.re - ζ.re)]
    have h2 : (z.im + h - ζ.im) ^ 2 ≤ (ζ₀.im + r + η) ^ 2 := by
      have hlo : 0 ≤ z.im + h - ζ.im := by linarith
      have hhi : z.im + h - ζ.im ≤ ζ₀.im + r + η := by linarith
      nlinarith
    linarith
  have hκ : crowdKappa ζ₀ h r η H * D ≤ 4 * h * (z.im - ζ.im) := by
    have hnum : 0 ≤ 4 * h * (ζ₀.im - h - r - η) := by
      have : 0 ≤ ζ₀.im - h - r - η := by linarith
      positivity
    calc crowdKappa ζ₀ h r η H * D ≤ crowdKappa ζ₀ h r η H * M := by
          refine mul_le_mul_of_nonneg_left hDM (div_nonneg hnum hMpos.le)
      _ = 4 * h * (ζ₀.im - h - r - η) := by
          rw [crowdKappa, div_mul_cancel₀ _ hMpos.ne']
      _ ≤ 4 * h * (z.im - ζ.im) := by
          have : ζ₀.im - h - r - η ≤ z.im - ζ.im := by linarith
          nlinarith
  rw [e]
  nlinarith

/-- **Rouché for the shift average.** If `p(· + ih)` vanishes at the centre of a circle on which
`‖p(z − ih)‖ < ‖p(z + ih)‖`, the shift average has a root inside. -/
theorem exists_zero_shiftAvg_of_norm_lt {p : ℝ[X]} {w₀ : ℂ} {h r : ℝ} (hr : 0 < r)
    (hroot : (p.map Complex.ofRealHom).eval (w₀ + h * I) = 0)
    (hlt : ∀ z ∈ sphere w₀ r, ‖(p.map Complex.ofRealHom).eval (z - h * I)‖ <
      ‖(p.map Complex.ofRealHom).eval (z + h * I)‖) :
    ∃ z ∈ ball w₀ r, ((GaloisForLFunctions.HTGeometry.shiftAvg h p).map Complex.ofRealHom).eval z = 0 := by
  set P := p.map Complex.ofRealHom with hP
  have hF : Differentiable ℂ (fun z => P.eval (z + h * I)) :=
    (P.differentiable.comp (differentiable_id.add_const _))
  have hG : Differentiable ℂ (fun z => P.eval (z + h * I) + P.eval (z - h * I)) :=
    hF.add (P.differentiable.comp (differentiable_id.sub_const _))
  obtain ⟨z, hz, hz0⟩ := exists_zero_mem_ball_of_norm_sub_lt hF hG hr
    (fun z hz => by simpa using hlt z hz) (mem_ball_self hr) hroot
  refine ⟨z, hz, ?_⟩
  rw [GaloisForLFunctions.HTGeometry.eval_map_shiftAvg, hz0, zero_div]

theorem prod_map_le_rpow_mul_prod {S : Multiset ℂ} {f g : ℂ → ℝ} {ρ : ℝ}
    (hf : ∀ ζ ∈ S, 0 ≤ f ζ) (hfg : ∀ ζ ∈ S, f ζ ≤ ρ * g ζ) :
    (S.map f).prod ≤ ρ ^ Multiset.card S * (S.map g).prod := by
  have h1 := Multiset.prod_map_le_prod_map₀ f (fun ζ => ρ * g ζ) hf hfg
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate] at h1
  exact h1

/-- **Crowded persistence (polynomials).** A root `ζ₀` of `p` with `η + r < Im ζ₀ − h`, whose
remaining roots split as `E + S` (`S` below height `η`, `E` with modulus ratio at most `B` on the
circle), gives a root of `cos(hD)p` within `r` of `ζ₀ − ih` once
`((2h + r)/r)·B·√(1 − κ)^N < 1`, `N` the number of neighbours in `S`. -/
theorem exists_zero_shiftAvg_near_deep_root {p : ℝ[X]} (hp : p ≠ 0) {ζ₀ : ℂ} {E S : Multiset ℂ}
    (hdecomp : (p.map Complex.ofRealHom).roots = ζ₀ ::ₘ (E + S)) {h r η H B : ℝ} (hh : 0 < h)
    (hr : 0 < r) (hη : 0 ≤ η) (hgap : η + r < ζ₀.im - h) (hS : ∀ ζ ∈ S, ζ.im ≤ η)
    (hEne : ∀ ζ ∈ E, ∀ z ∈ sphere (ζ₀ - h * I) r, z + h * I ≠ ζ)
    (hB : ∀ z ∈ sphere (ζ₀ - h * I) r,
      (E.map fun ζ => ‖z - h * I - ζ‖).prod ≤ B * (E.map fun ζ => ‖z + h * I - ζ‖).prod)
    (hcrowd : (2 * h + r) / r * B *
      Real.sqrt (1 - crowdKappa ζ₀ h r η H) ^ Multiset.card
        (S.filter fun ζ => |ζ.re - ζ₀.re| ≤ H ∧ -η ≤ ζ.im) < 1) :
    ∃ z, ‖z - (ζ₀ - h * I)‖ < r ∧ η < z.im ∧
      ((GaloisForLFunctions.HTGeometry.shiftAvg h p).map Complex.ofRealHom).eval z = 0 := by
  classical
  set P := p.map Complex.ofRealHom with hP
  have hP0 : P ≠ 0 := Polynomial.map_ne_zero hp
  set w₀ := ζ₀ - h * I with hw₀
  set ρ := Real.sqrt (1 - crowdKappa ζ₀ h r η H)
  set pnb : ℂ → Prop := fun ζ => |ζ.re - ζ₀.re| ≤ H ∧ -η ≤ ζ.im with hpnb
  set Snb := S.filter pnb with hSnb
  set Srest := S.filter fun ζ => ¬ pnb ζ with hSrest
  have hSsplit : S = Snb + Srest := (Multiset.filter_add_not pnb S).symm
  have hζ₀root : ζ₀ ∈ P.roots := by rw [hdecomp]; exact Multiset.mem_cons_self _ _
  -- the modulus through the roots
  have hnorm : ∀ W : ℂ, ‖P.eval W‖ = ‖P.leadingCoeff‖ * (‖W - ζ₀‖ *
      ((E.map fun ζ => ‖W - ζ‖).prod * ((Snb.map fun ζ => ‖W - ζ‖).prod *
        (Srest.map fun ζ => ‖W - ζ‖).prod))) := by
    intro W
    rw [norm_eval_eq_prod, hdecomp, Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
      Multiset.prod_add, hSsplit, Multiset.map_add, Multiset.prod_add]
  have hlt : ∀ z ∈ sphere w₀ r, ‖P.eval (z - h * I)‖ < ‖P.eval (z + h * I)‖ := by
    intro z hz
    have hzr : ‖z - w₀‖ = r := by simpa [dist_eq_norm] using hz
    have hzim : ζ₀.im - h - r ≤ z.im := by
      have := Complex.abs_im_le_norm (z - w₀)
      rw [hzr] at this
      have e : (z - w₀).im = z.im - (ζ₀.im - h) := by simp [hw₀]
      rw [e, abs_le] at this
      linarith
    -- the target factor
    have htargetP : ‖z + h * I - ζ₀‖ = r := by
      rw [show z + h * I - ζ₀ = z - w₀ by rw [hw₀]; ring, hzr]
    have htargetM : ‖z - h * I - ζ₀‖ ≤ 2 * h + r := by
      rw [show z - h * I - ζ₀ = (z - w₀) - (2 * h : ℝ) * I by rw [hw₀]; push_cast; ring]
      refine (norm_sub_le _ _).trans ?_
      rw [hzr, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg (by linarith)]
      linarith
    -- neighbours
    have hnb : (Snb.map fun ζ => ‖z - h * I - ζ‖).prod ≤
        ρ ^ Multiset.card Snb * (Snb.map fun ζ => ‖z + h * I - ζ‖).prod := by
      refine prod_map_le_rpow_mul_prod (fun _ _ => norm_nonneg _) ?_
      intro ζ hζ
      rw [hSnb, Multiset.mem_filter] at hζ
      have hsq := norm_sub_shift_sq_le_of_neighbour hh hr.le hη hgap hzr hζ.2.1 hζ.2.2
        (hS ζ hζ.1)
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul' _ (sq_nonneg _),
        Real.sqrt_sq (norm_nonneg _)] at this
    -- the rest of `S`
    have hrest : (Srest.map fun ζ => ‖z - h * I - ζ‖).prod ≤
        (Srest.map fun ζ => ‖z + h * I - ζ‖).prod := by
      refine Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => norm_nonneg _) fun ζ hζ => ?_
      rw [hSrest, Multiset.mem_filter] at hζ
      exact norm_sub_shift_le_of_im_le hh.le (by linarith [hS ζ hζ.1])
    -- nonvanishing at `z + ih`
    have hpos : 0 < ‖P.eval (z + h * I)‖ := by
      refine norm_pos_iff.mpr fun h0 => ?_
      have hmem : z + h * I ∈ P.roots := (mem_roots hP0).mpr h0
      rw [hdecomp, Multiset.mem_cons, Multiset.mem_add] at hmem
      rcases hmem with h1 | h1 | h1
      · have : z - w₀ = 0 := by rw [hw₀, ← h1]; ring
        rw [this, norm_zero] at hzr
        linarith
      · exact hEne _ h1 z hz rfl
      · have := hS _ h1
        simp at this
        linarith
    have hEb := hB z hz
    rw [hnorm] at hpos
    rw [hnorm, hnorm]
    rw [htargetP] at hpos ⊢
    set eP := (E.map fun ζ => ‖z + h * I - ζ‖).prod
    set eM := (E.map fun ζ => ‖z - h * I - ζ‖).prod
    set nP := (Snb.map fun ζ => ‖z + h * I - ζ‖).prod
    set nM := (Snb.map fun ζ => ‖z - h * I - ζ‖).prod
    set sP := (Srest.map fun ζ => ‖z + h * I - ζ‖).prod
    set sM := (Srest.map fun ζ => ‖z - h * I - ζ‖).prod
    have heM : 0 ≤ eM := Multiset.prod_nonneg fun _ h' => by
      obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp h'; exact norm_nonneg _
    have hnM : 0 ≤ nM := Multiset.prod_nonneg fun _ h' => by
      obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp h'; exact norm_nonneg _
    have hsM : 0 ≤ sM := Multiset.prod_nonneg fun _ h' => by
      obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp h'; exact norm_nonneg _
    have hnP : 0 ≤ nP := Multiset.prod_nonneg fun _ h' => by
      obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp h'; exact norm_nonneg _
    have hsP : 0 ≤ sP := Multiset.prod_nonneg fun _ h' => by
      obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp h'; exact norm_nonneg _
    have hlc : 0 ≤ ‖P.leadingCoeff‖ := norm_nonneg _
    have hρN : 0 ≤ ρ ^ Multiset.card Snb := pow_nonneg (Real.sqrt_nonneg _) _
    -- the main estimate
    have hall : ‖z - h * I - ζ₀‖ * (eM * (nM * sM)) ≤
        ((2 * h + r) / r * B * ρ ^ Multiset.card Snb) * (r * (eP * (nP * sP))) := by
      have hB0 : 0 ≤ B * eP := le_trans heM hEb
      calc ‖z - h * I - ζ₀‖ * (eM * (nM * sM))
          ≤ (2 * h + r) * ((B * eP) * ((ρ ^ Multiset.card Snb * nP) * sP)) := by
            gcongr
          _ = ((2 * h + r) / r * B * ρ ^ Multiset.card Snb) * (r * (eP * (nP * sP))) := by
            field_simp
    have hcore : 0 < r * (eP * (nP * sP)) := by
      have := hpos
      rw [mul_pos_iff_of_pos_left] at this
      · exact this
      · exact norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP0)
    calc ‖P.leadingCoeff‖ * (‖z - h * I - ζ₀‖ * (eM * (nM * sM)))
        ≤ ‖P.leadingCoeff‖ * (((2 * h + r) / r * B * ρ ^ Multiset.card Snb) *
          (r * (eP * (nP * sP)))) := mul_le_mul_of_nonneg_left hall hlc
      _ < ‖P.leadingCoeff‖ * (r * (eP * (nP * sP))) := by
          refine mul_lt_mul_of_pos_left ?_ (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hP0))
          calc ((2 * h + r) / r * B * ρ ^ Multiset.card Snb) * (r * (eP * (nP * sP)))
              < 1 * (r * (eP * (nP * sP))) := mul_lt_mul_of_pos_right hcrowd hcore
            _ = r * (eP * (nP * sP)) := one_mul _
  have hroot : P.eval (w₀ + h * I) = 0 := by
    rw [show w₀ + h * I = ζ₀ by rw [hw₀]; ring]
    exact (mem_roots hP0).mp hζ₀root
  obtain ⟨z, hz, hz0⟩ := exists_zero_shiftAvg_of_norm_lt hr hroot hlt
  refine ⟨z, by simpa [dist_eq_norm] using hz, ?_, hz0⟩
  have := Complex.abs_im_le_norm (z - w₀)
  have hzr : ‖z - w₀‖ < r := by simpa [dist_eq_norm] using hz
  have e : (z - w₀).im = z.im - (ζ₀.im - h) := by simp [hw₀]
  rw [e, abs_le] at this
  linarith

end

end RHTower.CrowdedPersistence
