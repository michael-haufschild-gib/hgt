import GaloisForLFunctions.HyperbolicArakelovTheory.CarriersAlongAnEndOfBoundedSelfEnergy

/-!
# The boundary of a group with convergent Poincaré series at `½`

B118′.2 asks whether a twisted Green sum `Σ_{γ≠1} χ(γ)·2πG_{1/2}(d(z_m, γz_n))` of a discrete group
`Γ ⊂ SL₂(ℂ)` whose Poincaré series converges at `½` can equal the torsion kernel. The answer depends on
the position of the end `∞` of the degree geodesic in `∂ℍ³ = Ω(Γ) ⊔ Λ(Γ)`. This file settles the
positions left open by the earlier carriers.

**Theorems.**
* `not_summable_poincareWeight_of_parabolic`: **convergence at `½` excludes parabolic elements.** For
  `tr γ = 2`, `γ ≠ 1`, `N = γ − 1` squares to zero, `γ^k = 1 + kN`, and
  `cosh d(z_1, γ^k z_1) = ½‖1 + kN‖² ≤ 2(1 + k‖N‖)²`, so the weights `e^{−d/2}` are `≥ c/k`: the
  cyclic subgroup alone has a harmonic Poincaré series. For `tr γ = −2`, `γ ≠ −1`, pass to `γ²`.
* `endpointEisenstein_of_wandering`, `not_carrierSum_eq_torsion_of_wandering`: if `∞ ∈ Ω(Γ)`, i.e.
  `{‖z‖ > R}` meets its image under finitely many elements (`WanderingEnd`), then every other element has
  `c ≠ 0`, `‖a‖, ‖d‖ ≤ R‖c‖` and `‖c‖ ≥ 1/(2R + 1)` (test points `T`, `−d/c + T` and `−d/c + δ`, with
  `γ(−d/c + w) = a/c − 1/(c²w)`), which is the endpoint Eisenstein condition: no carrier.
* `not_carrierSum_eq_torsion_of_convergent`: no carrier if `∞` is a point of discontinuity or the
  self-energy stays bounded along the degree end (in particular at a conical limit point).

**Scope (classical inputs).** A geometrically finite group has limit set = conical points ∪ bounded
parabolic fixed points (Beardon–Maskit); without parabolic elements every limit point is conical. A
finitely generated group with `δ(Γ) < 2` is geometrically finite (Canary, with the tameness theorem of
Agol and Calegari–Gabai). So B118′.2 has a negative answer for every finitely generated discrete
group with convergent Poincaré series at `½`, in particular for the geometrically finite groups with
`δ < ½` and Schottky characters of the question.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-! ## Convergence at `½` excludes parabolic elements -/

/-- A parabolic element of `SL₂(ℂ)`: trace `±2` and not `±1`. -/
def IsParabolic (g : SL2C) : Prop :=
  ((g : Matrix (Fin 2) (Fin 2) ℂ).trace = 2 ∧ g ≠ 1) ∨
    ((g : Matrix (Fin 2) (Fin 2) ℂ).trace = -2 ∧ (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1)

theorem det_entries (g : SL2C) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have := g.2; rwa [Matrix.det_fin_two] at this

/-- For trace `2` the nilpotent part `N = γ − 1` squares to zero. -/
theorem sub_one_mul_self_of_trace_eq_two {g : SL2C}
    (h : (g : Matrix (Fin 2) (Fin 2) ℂ).trace = 2) :
    ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
  have hdet := det_entries g
  rw [Matrix.trace_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination (-1 : ℂ) * hdet + g.1 0 0 * h
  · linear_combination g.1 0 1 * h
  · linear_combination g.1 1 0 * h
  · linear_combination (-1 : ℂ) * hdet + g.1 1 1 * h

theorem one_add_pow_of_mul_self_eq_zero {N : Matrix (Fin 2) (Fin 2) ℂ} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : ℂ) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hN, smul_zero, add_zero,
      Nat.cast_succ, add_smul, one_smul]
    abel

/-- Powers of a unipotent element: `γ^k = 1 + kN`. -/
theorem coe_pow_of_trace_eq_two {g : SL2C} (h : (g : Matrix (Fin 2) (Fin 2) ℂ).trace = 2)
    (k : ℕ) : ((g ^ k : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
      1 + (k : ℂ) • ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  calc (g : Matrix (Fin 2) (Fin 2) ℂ) ^ k = (1 + ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)) ^ k := by
        rw [add_sub_cancel]
    _ = _ := one_add_pow_of_mul_self_eq_zero (sub_one_mul_self_of_trace_eq_two h) k

/-- The orbit of a unipotent element grows at most linearly: `cosh d(z_1, γ^k z_1) ≤ 2(1 + kν)²`. -/
theorem imageCosh_pow_le {g : SL2C} (h : (g : Matrix (Fin 2) (Fin 2) ℂ).trace = 2) (k : ℕ) :
    imageCosh (g ^ k) 1 1 ≤ 2 * (1 + k * (‖g.1 0 0 - 1‖ + ‖g.1 0 1‖ + ‖g.1 1 0‖ + ‖g.1 1 1 - 1‖)) ^ 2 := by
  set ν := ‖g.1 0 0 - 1‖ + ‖g.1 0 1‖ + ‖g.1 1 0‖ + ‖g.1 1 1 - 1‖ with hν
  have hpow := coe_pow_of_trace_eq_two h k
  have he : ∀ i j, (g ^ k).1 i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
      (k : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j) := by
    intro i j
    have := congr_fun (congr_fun hpow i) j
    simpa [Matrix.add_apply, Matrix.smul_apply] using this
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb : ∀ i j, ‖(g ^ k).1 i j‖ ≤ 1 + k * ν := by
    have n1 := norm_nonneg (g.1 0 0 - 1)
    have n2 := norm_nonneg (g.1 0 1)
    have n3 := norm_nonneg (g.1 1 0)
    have n4 := norm_nonneg (g.1 1 1 - 1)
    have h00 : ‖g.1 0 0 - 1‖ ≤ ν := by linarith
    have h01 : ‖g.1 0 1‖ ≤ ν := by linarith
    have h10 : ‖g.1 1 0‖ ≤ ν := by linarith
    have h11 : ‖g.1 1 1 - 1‖ ≤ ν := by linarith
    intro i j
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast]
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith
  have hk : 0 ≤ 1 + k * ν := by positivity
  have hsq : ∀ i j, ‖(g ^ k).1 i j‖ ^ 2 ≤ (1 + k * ν) ^ 2 := fun i j =>
    pow_le_pow_left₀ (norm_nonneg _) (hb i j) 2
  unfold imageCosh
  have := hsq 0 0; have := hsq 0 1; have := hsq 1 0; have := hsq 1 1
  rw [div_le_iff₀ (by norm_num)]
  simp only [one_pow, mul_one]
  linarith

/-- The Poincaré weight of `γ^k` is at least `1/(2(1 + kν))`. -/
theorem poincareWeight_pow_ge {g : SL2C} (h : (g : Matrix (Fin 2) (Fin 2) ℂ).trace = 2) (k : ℕ) :
    1 / (2 * (1 + k * (‖g.1 0 0 - 1‖ + ‖g.1 0 1‖ + ‖g.1 1 0‖ + ‖g.1 1 1 - 1‖))) ≤
      poincareWeight (g ^ k) := by
  set ν := ‖g.1 0 0 - 1‖ + ‖g.1 0 1‖ + ‖g.1 1 0‖ + ‖g.1 1 1 - 1‖ with hν
  set X := imageCosh (g ^ k) 1 1 with hX
  have hX1 : 1 ≤ X := one_le_imageCosh _ one_pos one_pos
  have hXle := imageCosh_pow_le h k
  have hk : 0 < 1 + k * ν := by positivity
  have hw : poincareWeight (g ^ k) = Real.exp (-(Real.arcosh X) / 2) := by
    rw [poincareWeight, h3Dist_degPoint_h3Act]
  have h1 := inv_sqrt_le_exp_arcosh hX1
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hsX : Real.sqrt X ≤ Real.sqrt 2 * (1 + k * ν) := by
    rw [← Real.sqrt_sq hk.le, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hXle
  have hsXpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
  have h2 : (Real.sqrt 2 * (1 + k * ν))⁻¹ ≤ (Real.sqrt X)⁻¹ := inv_anti₀ hsXpos hsX
  rw [hw]
  have h3 : 1 / (2 * (1 + k * ν)) = (Real.sqrt 2 * (1 + k * ν))⁻¹ / Real.sqrt 2 := by
    field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h3, div_le_iff₀ hs2pos]
  nlinarith

/-- **A parabolic element makes the Poincaré series at `½` diverge.** -/
theorem not_summable_poincareWeight_of_parabolic {Γ : Subgroup SL2C} {g : SL2C} (hg : g ∈ Γ)
    (hpar : IsParabolic g) : ¬ Summable fun i : Nontriv Γ => poincareWeight i.1 := by
  -- reduce to trace `2`
  obtain ⟨u, hu, htr, hu1⟩ : ∃ u ∈ Γ, (u : Matrix (Fin 2) (Fin 2) ℂ).trace = 2 ∧ u ≠ 1 := by
    rcases hpar with ⟨htr, hne⟩ | ⟨htr, hne⟩
    · exact ⟨g, hg, htr, hne⟩
    · refine ⟨g ^ 2, Γ.pow_mem hg 2, ?_, ?_⟩
      · have hdet := det_entries g
        rw [Matrix.trace_fin_two] at htr
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.trace_fin_two, sq]
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (g.1 0 0 + g.1 1 1 - 2) * htr - 2 * hdet
      · intro h1
        have hsq : (g : Matrix (Fin 2) (Fin 2) ℂ) * g = 1 := by
          have := congr_arg (fun x : SL2C => (x : Matrix (Fin 2) (Fin 2) ℂ)) h1
          simpa [sq] using this
        have hdet := det_entries g
        rw [Matrix.trace_fin_two] at htr
        have e01 := congr_fun (congr_fun hsq 0) 1
        have e10 := congr_fun (congr_fun hsq 1) 0
        have e00 := congr_fun (congr_fun hsq 0) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at e01 e10 e00
        norm_num at e01 e10 e00
        have hb : g.1 0 1 = 0 := by linear_combination (-1 / 2 : ℂ) * e01 + (g.1 0 1 / 2) * htr
        have hc : g.1 1 0 = 0 := by linear_combination (-1 / 2 : ℂ) * e10 + (g.1 1 0 / 2) * htr
        have ha : (g.1 0 0 + 1) ^ 2 = 0 := by
          linear_combination (-1 : ℂ) * hdet + g.1 0 0 * htr - g.1 1 0 * hb
        have ha' : g.1 0 0 = -1 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha
          linear_combination this
        have hd' : g.1 1 1 = -1 := by linear_combination htr - ha'
        apply hne
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha', hb, hc, hd']
  -- the cyclic subgroup injects into `Γ∖{1}`
  set N := (u : Matrix (Fin 2) (Fin 2) ℂ) - 1 with hN
  have hN0 : N ≠ 0 := fun h => hu1 (Subtype.ext (by rw [hN, sub_eq_zero] at h; simpa using h))
  have hne : ∀ k : ℕ, u ^ (k + 1) ≠ 1 := by
    intro k h
    have := congr_arg (fun x : SL2C => (x : Matrix (Fin 2) (Fin 2) ℂ)) h
    simp only [coe_pow_of_trace_eq_two htr, Matrix.SpecialLinearGroup.coe_one, add_eq_left] at this
    exact hN0 ((smul_eq_zero.mp this).resolve_left (by exact_mod_cast Nat.succ_ne_zero k))
  let φ : ℕ → Nontriv Γ := fun k => ⟨u ^ (k + 1), Γ.pow_mem hu _, hne k⟩
  have hφ : Function.Injective φ := by
    intro k j hkj
    have h1 := congr_arg (fun x : Nontriv Γ => ((x.1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) hkj
    simp only [φ, coe_pow_of_trace_eq_two htr, add_right_inj] at h1
    simpa using smul_left_injective ℂ hN0 h1
  intro hsum
  have hcomp := hsum.comp_injective hφ
  set ν := ‖u.1 0 0 - 1‖ + ‖u.1 0 1‖ + ‖u.1 1 0‖ + ‖u.1 1 1 - 1‖ with hν
  have hν0 : 0 ≤ ν := by positivity
  set c := 1 / (2 * (1 + ν)) with hc
  have hc0 : 0 < c := by positivity
  have hlow : ∀ k : ℕ, c * (1 / ((k + 1 : ℕ) : ℝ)) ≤ poincareWeight (φ k).1 := by
    intro k
    refine le_trans ?_ (poincareWeight_pow_ge htr (k + 1))
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    rw [hc, div_mul_div_comm, one_mul, one_div_le_one_div (by positivity) (by positivity)]
    nlinarith
  have hharm : Summable fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) :=
    (summable_mul_left_iff hc0.ne').mp
      (Summable.of_nonneg_of_le (fun k => by positivity) hlow hcomp)
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hharm)

/-- Under convergence at `½`, `Γ` has no parabolic element. -/
theorem not_isParabolic_of_summable {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {g : SL2C} (hg : g ∈ Γ) :
    ¬ IsParabolic g := fun hpar => not_summable_poincareWeight_of_parabolic hg hpar hP

/-! ## Points of discontinuity -/

/-- The Möbius action of `γ` on `ℂ`. -/
def mobius (g : SL2C) (z : ℂ) : ℂ := (g.1 0 0 * z + g.1 0 1) / (g.1 1 0 * z + g.1 1 1)

/-- **`∞` is a point of discontinuity** of the family: the neighbourhood `{‖z‖ > R}` meets its image
under only finitely many `γ_i`. -/
def WanderingEnd {ι : Type*} (γ : ι → SL2C) (R : ℝ) : Prop :=
  {i | ∃ z : ℂ, R < ‖z‖ ∧ (γ i).1 1 0 * z + (γ i).1 1 1 ≠ 0 ∧ R < ‖mobius (γ i) z‖}.Finite

/-- `γ` maps `{‖z‖ > R}` into `{‖z‖ ≤ R}`. -/
def MapsOff (g : SL2C) (R : ℝ) : Prop :=
  ∀ z : ℂ, R < ‖z‖ → g.1 1 0 * z + g.1 1 1 ≠ 0 → ‖mobius g z‖ ≤ R

/-- Near the pole: `γ(−d/c + w) = a/c − 1/(c²w)`. -/
theorem mobius_shift {g : SL2C} (hc : g.1 1 0 ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    g.1 1 0 * (-(g.1 1 1) / g.1 1 0 + w) + g.1 1 1 = g.1 1 0 * w ∧
      mobius g (-(g.1 1 1) / g.1 1 0 + w) = g.1 0 0 / g.1 1 0 - 1 / (g.1 1 0 ^ 2 * w) := by
  have hdet := det_entries g
  have h1 : g.1 1 0 * (-(g.1 1 1) / g.1 1 0 + w) + g.1 1 1 = g.1 1 0 * w := by
    field_simp; ring
  refine ⟨h1, ?_⟩
  unfold mobius
  rw [h1]
  field_simp
  linear_combination (-1 : ℂ) * hdet

/-- Lower bounds for `‖γ(−d/c + T)‖` with `T > 0` real. -/
theorem norm_mobius_shift_ge {g : SL2C} (hc : g.1 1 0 ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖g.1 0 0‖ / ‖g.1 1 0‖ - 1 / (‖g.1 1 0‖ ^ 2 * T) ≤ ‖mobius g (-(g.1 1 1) / g.1 1 0 + T)‖ ∧
      1 / (‖g.1 1 0‖ ^ 2 * T) - ‖g.1 0 0‖ / ‖g.1 1 0‖ ≤ ‖mobius g (-(g.1 1 1) / g.1 1 0 + T)‖ := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [(mobius_shift hc hT').2]
  have hA : ‖g.1 0 0 / g.1 1 0‖ = ‖g.1 0 0‖ / ‖g.1 1 0‖ := norm_div _ _
  have hB : ‖1 / (g.1 1 0 ^ 2 * (T : ℂ))‖ = 1 / (‖g.1 1 0‖ ^ 2 * T) := by
    rw [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le]
  constructor
  · have := norm_sub_norm_le (g.1 0 0 / g.1 1 0) (1 / (g.1 1 0 ^ 2 * (T : ℂ)))
    rw [hA, hB] at this; exact this
  · have := norm_sub_norm_le (1 / (g.1 1 0 ^ 2 * (T : ℂ))) (g.1 0 0 / g.1 1 0)
    rw [hA, hB, norm_sub_rev] at this; exact this

/-- `‖−d/c + T‖ ≥ T − ‖d‖/‖c‖`. -/
theorem norm_shift_ge (g : SL2C) (T : ℝ) :
    T - ‖g.1 1 1‖ / ‖g.1 1 0‖ ≤ ‖-(g.1 1 1) / g.1 1 0 + (T : ℂ)‖ := by
  have h := norm_sub_norm_le ((T : ℂ)) (g.1 1 1 / g.1 1 0)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs] at h
  have e : (T : ℂ) - g.1 1 1 / g.1 1 0 = -(g.1 1 1) / g.1 1 0 + T := by ring
  rw [e] at h
  linarith [le_abs_self T]

theorem ne_zero_of_mapsOff {g : SL2C} {R : ℝ} (hR : 0 < R) (he : MapsOff g R) : g.1 1 0 ≠ 0 := by
  intro hc
  have hdet := det_entries g
  rw [hc, mul_zero, sub_zero] at hdet
  have ha : g.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hd : g.1 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have ha0 : 0 < ‖g.1 0 0‖ := norm_pos_iff.mpr ha
  have hd0 : 0 < ‖g.1 1 1‖ := norm_pos_iff.mpr hd
  set T := R + 1 + ((R + 1) * ‖g.1 1 1‖ + ‖g.1 0 1‖) / ‖g.1 0 0‖ with hT
  have hfrac : 0 ≤ ((R + 1) * ‖g.1 1 1‖ + ‖g.1 0 1‖) / ‖g.1 0 0‖ := by positivity
  have hTR : R < ‖(T : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hden : g.1 1 0 * (T : ℂ) + g.1 1 1 ≠ 0 := by rw [hc, zero_mul, zero_add]; exact hd
  have hle := he T hTR hden
  rw [mobius, hc, zero_mul, zero_add, norm_div] at hle
  have hnum : (R + 1) * ‖g.1 1 1‖ ≤ ‖g.1 0 0 * T + g.1 0 1‖ := by
    have h1 := norm_sub_norm_le (g.1 0 0 * (T : ℂ)) (-(g.1 0 1))
    rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)] at h1
    have h2 : ‖g.1 0 0‖ * T ≥ (R + 1) * ‖g.1 1 1‖ + ‖g.1 0 1‖ := by
      have : ‖g.1 0 0‖ * (((R + 1) * ‖g.1 1 1‖ + ‖g.1 0 1‖) / ‖g.1 0 0‖) =
          (R + 1) * ‖g.1 1 1‖ + ‖g.1 0 1‖ := by field_simp
      nlinarith
    linarith
  rw [div_le_iff₀ hd0] at hle
  nlinarith

theorem norm_a_le_of_mapsOff {g : SL2C} {R : ℝ} (hR : 0 < R) (he : MapsOff g R)
    (hc : g.1 1 0 ≠ 0) : ‖g.1 0 0‖ ≤ R * ‖g.1 1 0‖ := by
  have hc0 : 0 < ‖g.1 1 0‖ := norm_pos_iff.mpr hc
  by_contra hlt
  push Not at hlt
  set q := ‖g.1 0 0‖ / ‖g.1 1 0‖ with hq
  have hqR : R < q := by rw [hq, lt_div_iff₀ hc0]; linarith
  set ε := q - R with hε
  have hε0 : 0 < ε := by linarith
  set T := R + 1 + ‖g.1 1 1‖ / ‖g.1 1 0‖ + 2 / (‖g.1 1 0‖ ^ 2 * ε) with hT
  have h2 : 0 ≤ 2 / (‖g.1 1 0‖ ^ 2 * ε) := by positivity
  have h3 : 0 ≤ ‖g.1 1 1‖ / ‖g.1 1 0‖ := by positivity
  have hT0 : 0 < T := by linarith
  have hzR : R < ‖-(g.1 1 1) / g.1 1 0 + (T : ℂ)‖ := by
    have := norm_shift_ge g T; linarith
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hle := he _ hzR (by rw [(mobius_shift hc hT').1]; exact mul_ne_zero hc hT')
  have hge := (norm_mobius_shift_ge hc hT0).1
  have hsmall : 1 / (‖g.1 1 0‖ ^ 2 * T) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hT2 : 2 / (‖g.1 1 0‖ ^ 2 * ε) ≤ T := by linarith
    rw [div_le_iff₀ (by positivity)] at hT2
    nlinarith
  rw [← hq] at hge
  linarith

theorem norm_d_le_of_mapsOff {g : SL2C} {R : ℝ} (hR : 0 < R) (he : MapsOff g R)
    (hc : g.1 1 0 ≠ 0) : ‖g.1 1 1‖ ≤ R * ‖g.1 1 0‖ := by
  have hc0 : 0 < ‖g.1 1 0‖ := norm_pos_iff.mpr hc
  have ha := norm_a_le_of_mapsOff hR he hc
  by_contra hlt
  push Not at hlt
  set q := ‖g.1 1 1‖ / ‖g.1 1 0‖ with hq
  have hqR : R < q := by rw [hq, lt_div_iff₀ hc0]; linarith
  set δ := min ((q - R) / 2) (1 / (4 * R * ‖g.1 1 0‖ ^ 2)) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ (q - R) / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (4 * R * ‖g.1 1 0‖ ^ 2) := min_le_right _ _
  have hzR : R < ‖-(g.1 1 1) / g.1 1 0 + (δ : ℂ)‖ := by
    have h := norm_sub_norm_le (-(g.1 1 1) / g.1 1 0) (-(δ : ℂ))
    rw [sub_neg_eq_add, norm_neg, norm_div, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le, ← hq] at h
    linarith
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ0.ne'
  have hle := he _ hzR (by rw [(mobius_shift hc hδ').1]; exact mul_ne_zero hc hδ')
  have hge := (norm_mobius_shift_ge hc hδ0).2
  have hbig : 4 * R ≤ 1 / (‖g.1 1 0‖ ^ 2 * δ) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδ2
    nlinarith
  have haq : ‖g.1 0 0‖ / ‖g.1 1 0‖ ≤ R := by rw [div_le_iff₀ hc0]; exact ha
  linarith

theorem one_le_of_mapsOff {g : SL2C} {R : ℝ} (hR : 0 < R) (he : MapsOff g R)
    (hc : g.1 1 0 ≠ 0) : 1 ≤ (2 * R + 1) * ‖g.1 1 0‖ := by
  have hc0 : 0 < ‖g.1 1 0‖ := norm_pos_iff.mpr hc
  have ha : ‖g.1 0 0‖ / ‖g.1 1 0‖ ≤ R := by
    rw [div_le_iff₀ hc0]; exact norm_a_le_of_mapsOff hR he hc
  have hd : ‖g.1 1 1‖ / ‖g.1 1 0‖ ≤ R := by
    rw [div_le_iff₀ hc0]; exact norm_d_le_of_mapsOff hR he hc
  set T := 2 * R + 1 with hT
  have hT0 : 0 < T := by linarith
  have hzR : R < ‖-(g.1 1 1) / g.1 1 0 + (T : ℂ)‖ := by
    have := norm_shift_ge g T; linarith
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hle := he _ hzR (by rw [(mobius_shift hc hT').1]; exact mul_ne_zero hc hT')
  have hge := (norm_mobius_shift_ge hc hT0).2
  by_contra hlt
  push Not at hlt
  have hsq : (T * ‖g.1 1 0‖) ^ 2 < 1 := by
    have h0 : 0 ≤ T * ‖g.1 1 0‖ := by positivity
    nlinarith
  have hbig : T < 1 / (‖g.1 1 0‖ ^ 2 * T) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- **A point of discontinuity is an Eisenstein end.** -/
theorem endpointEisenstein_of_wandering {ι : Type*} {γ : ι → SL2C}
    (hP : Summable fun i => poincareWeight (γ i)) {R : ℝ} (hR : 0 < R) (hW : WanderingEnd γ R) :
    EndpointEisenstein γ := by
  set E := {i | ∃ z : ℂ, R < ‖z‖ ∧ (γ i).1 1 0 * z + (γ i).1 1 1 ≠ 0 ∧
    R < ‖mobius (γ i) z‖} with hE
  have hesc : ∀ i ∉ E, MapsOff (γ i) R := fun i hi z hz hcz => by
    by_contra h; push Not at h; exact hi ⟨z, hz, hcz, h⟩
  have hstab : {i | (γ i).1 1 0 = 0}.Finite :=
    hW.subset fun i hi => by
      by_contra hn; exact ne_zero_of_mapsOff hR (hesc i hn) hi
  set f : ι → ℝ := fun i => (‖(γ i).1 0 0‖ + ‖(γ i).1 1 1‖ + 1) / ‖(γ i).1 1 0‖ with hf
  obtain ⟨R₀, hR₀⟩ := (hW.image f).bddAbove
  set R' := max (2 * R + 1) R₀ with hR'
  have hR'0 : 0 < R' := lt_max_of_lt_left (by linarith)
  have hRR' : R ≤ R' := le_trans (by linarith) (le_max_left _ _)
  refine endpointEisenstein_of_poincare hR'0 hP (fun i hc => ?_) hstab
  have hc0 : 0 < ‖(γ i).1 1 0‖ := norm_pos_iff.mpr hc
  by_cases hi : i ∈ E
  · have hfi : f i ≤ R₀ := hR₀ ⟨i, hi, rfl⟩
    have h1 : ‖(γ i).1 0 0‖ + ‖(γ i).1 1 1‖ + 1 ≤ R₀ * ‖(γ i).1 1 0‖ := by
      rwa [hf, div_le_iff₀ hc0] at hfi
    have h2 : R₀ * ‖(γ i).1 1 0‖ ≤ R' * ‖(γ i).1 1 0‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hc0.le
    have := norm_nonneg ((γ i).1 0 0)
    have := norm_nonneg ((γ i).1 1 1)
    exact ⟨by linarith, by linarith, by linarith⟩
  · have he := hesc i hi
    have hle : ∀ x : ℝ, x ≤ R' → x * ‖(γ i).1 1 0‖ ≤ R' * ‖(γ i).1 1 0‖ := fun x hx =>
      mul_le_mul_of_nonneg_right hx hc0.le
    exact ⟨(norm_a_le_of_mapsOff hR he hc).trans (hle R hRR'),
      (norm_d_le_of_mapsOff hR he hc).trans (hle R hRR'),
      (one_le_of_mapsOff hR he hc).trans (hle _ (le_max_left _ _))⟩

/-- **B118′.2 at a point of discontinuity.** -/
theorem not_carrierSum_eq_torsion_of_wandering {ι : Type*} {γ : ι → SL2C} {w : ι → ℂ}
    (hP : Summable fun i => poincareWeight (γ i)) {R : ℝ} (hR : 0 < R) (hW : WanderingEnd γ R)
    (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum γ w m n = κ * (weilPrimeKernel m n : ℂ) :=
  not_carrierSum_eq_torsion (endpointEisenstein_of_wandering hP hR hW) hw hκ

/-- **B118′.2 for a group convergent at `½`.** Let `Γ ⊂ SL₂(ℂ)` have convergent Poincaré series at
`½`. If `∞` is a point of discontinuity of `Γ`, or the self-energy of `Γ\ℍ³` stays bounded along
the degree end (as at every conical limit point), then for every weight `‖w‖ ≤ 1` on `Γ∖{1}` and
every `κ ≠ 0` the twisted Green sum is not `κ` times the torsion kernel. -/
theorem not_carrierSum_eq_torsion_of_convergent {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1)
    (hend : (∃ R, 0 < R ∧ WanderingEnd (fun i : Nontriv Γ => i.1) R) ∨
      ∃ C, ∃ᶠ M : ℕ in atTop, selfEnergy Γ M ≤ C)
    {w : Nontriv Γ → ℂ} (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum (fun i : Nontriv Γ => i.1) w m n = κ * (weilPrimeKernel m n : ℂ) := by
  rcases hend with ⟨R, hR, hW⟩ | ⟨C, hD⟩
  · exact not_carrierSum_eq_torsion_of_wandering hP hR hW hw hκ
  · exact not_carrierSum_eq_torsion_of_selfEnergy hP hD hw hκ

end GaloisForLFunctions.HyperbolicArakelovTheory
