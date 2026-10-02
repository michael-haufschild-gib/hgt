import GaloisForLFunctions.RHTower.GammaRPowFunctionalEquationAbundance

/-!
# Odd functional equations of `ζ(s)^d`-type: anti-twins

`gammaRPow_odd_functional_equation_abundance`: for `d = k+1 ≥ 3` and every `N` there are infinitely
many linearly independent Dirichlet series, vanishing below `N`, whose completions
`Γ_ℝ(s)^d Σ e_n (n+1)^{-s}` are entire and satisfy `Λ(1-s) = -Λ(s)` (root number `-1`).
In degree 1 there are none (odd Hamburger).

Proof: the even proof with the roles of the two Voronoi eigenspaces exchanged.
* Relations now annihilate the **symmetric** chart class `Φ(w) = m_d(w)Φ(1-w)`. The derivative
  bound is the antisymmetric one applied to `-m_d`.
* The relations are tested on `K_k(yx) + y⁻¹K_k(x/y)`, giving the odd theta relation
  `θ(1/y) = -yθ(y)`.
* Hecke's argument with root number `-1` gives the completion.

Together with the even twins, these supply the Hermite–Biehler pairs `(E, A)`, `E` even and `A` odd:
`E` is real-rooted whenever `Re(A/E) > 0` on `Re s > 1/2`.
-/

open Complex MeasureTheory Set Asymptotics Filter Topology

noncomputable section

namespace RHTower

/-- The odd theta symmetry `θ(1/y) = -y θ(y)` transports rapid decay at infinity to rapid decay
at zero. -/
theorem rapidDecayRay_of_theta_antisymm {θ : ℝ → ℂ} (hc : ContinuousOn θ (Ioi 0))
    (hdec : ∀ a : ℝ, θ =O[atTop] fun x : ℝ => x ^ (-a))
    (hanti : ∀ y : ℝ, 0 < y → θ (1 / y) = -((y : ℂ) * θ y)) : RapidDecayRay θ := by
  refine ⟨hc, hdec, fun b => ?_⟩
  have h1 := (hdec (1 - b)).comp_tendsto tendsto_inv_nhdsGT_zero
  have h2 : (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) =O[𝓝[>] 0] fun x : ℝ => x⁻¹ := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    simp
  have h3 := (h2.mul h1).neg_left
  refine h3.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    have := hanti x⁻¹ (inv_pos.mpr hx')
    rw [one_div, inv_inv] at this
    simp [Function.comp, this]
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    simp only [Function.comp]
    rw [Real.inv_rpow hx'.le, Real.rpow_neg hx'.le, inv_inv, Real.rpow_sub hx', Real.rpow_one,
      Real.rpow_neg hx'.le]
    field_simp

/-- The odd theta symmetry gives `Λ(1 - s) = -Λ(s)` for the Mellin transform. -/
theorem mellin_one_sub_eq_neg_of_theta_antisymm {θ : ℝ → ℂ}
    (hanti : ∀ y : ℝ, 0 < y → θ (1 / y) = -((y : ℂ) * θ y)) (s : ℂ) :
    mellin θ (1 - s) = -mellin θ s := by
  have h : mellin θ s = mellin (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ) •
      ((fun u : ℝ => (-1 : ℂ) • θ u) t⁻¹)) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    have := hanti t⁻¹ (inv_pos.mpr ht')
    rw [one_div, inv_inv] at this
    simp only [smul_eq_mul]
    rw [this, Complex.cpow_neg_one]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
    push_cast
    field_simp
  rw [mellin_cpow_smul (fun t : ℝ => (fun u : ℝ => (-1 : ℂ) • θ u) t⁻¹),
    mellin_comp_inv (fun u : ℝ => (-1 : ℂ) • θ u), mellin_const_smul θ] at h
  have e : -(s + -1) = 1 - s := by ring
  rw [e, smul_eq_mul] at h
  linear_combination h

/-- **Hecke's converse with root number `-1`.** -/
theorem hecke_theta_converse_odd {K : ℝ → ℂ} {e : ℕ → ℂ} {A C : ℝ}
    (hK : ContinuousOn K (Ioi 0))
    (he : ∀ n : ℕ, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    (hθc : ContinuousOn (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) (Ioi 0))
    (hθdec : ∀ a : ℝ, (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) =O[atTop]
      fun x : ℝ => x ^ (-a))
    (hθanti : ∀ y : ℝ, 0 < y → (∑' n : ℕ, e n * K (((n : ℝ) + 1) * (1 / y)))
      = -((y : ℂ) * ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y))) :
    Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) ∧
    (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) (1 - s)
      = -mellin (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) s) ∧
    (∀ s : ℂ, A + 1 < s.re → IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖K t‖) (Ioi 0) →
      mellin (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) s
        = (∑' n : ℕ, e n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * mellin K s) :=
  ⟨differentiable_mellin_of_rapidDecayRay (rapidDecayRay_of_theta_antisymm hθc hθdec hθanti),
    mellin_one_sub_eq_neg_of_theta_antisymm hθanti,
    fun _ hs hKint => mellin_tsum_kernel hK hKint he hs⟩

private theorem integrableOn_rpow_mul_norm_of_mellinConvergent {f : ℝ → ℂ} {c : ℝ}
    (h : MellinConvergent f (c : ℂ)) :
    IntegrableOn (fun y : ℝ => y ^ (c - 1) * ‖f y‖) (Ioi 0) := by
  have h' : IntegrableOn (fun y : ℝ => ‖(y : ℂ) ^ ((c : ℂ) - 1) • f y‖) (Ioi 0) := h.norm
  refine h'.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy' : (0 : ℝ) < y := hy
  show ‖(y : ℂ) ^ ((c : ℂ) - 1) • f y‖ = y ^ (c - 1) * ‖f y‖
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hy']
  simp

private theorem summable_succ_rpow {p : ℝ} (hp : p < -1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ p := by
  have := (Real.summable_nat_rpow (p := p)).mpr hp
  exact ((summable_nat_add_iff 1).mpr this).congr (fun n => by push_cast; ring_nf)

private theorem norm_theta_term_le (d : ℕ) {e : ℕ → ℂ} {A C c : ℝ} (_hc : 0 < c)
    (he : ∀ n : ℕ, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ A) {K : ℝ}
    (hK : ∀ x : ℝ, 0 < x → ‖gammaRPowKernel d x‖ ≤ K * x ^ (-c)) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖e n * gammaRPowKernel d (((n : ℝ) + 1) * y)‖ ≤ C * K * y ^ (-c) * ((n : ℝ) + 1) ^ (A - c) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hK0 : 0 ≤ K := by
    have := hK 1 one_pos; rw [Real.one_rpow, mul_one] at this; exact le_trans (norm_nonneg _) this
  rw [norm_mul]
  have h1 := hK _ (mul_pos hn hy)
  rw [Real.mul_rpow hn.le hy.le] at h1
  have hC0 : 0 ≤ C := by
    have := he 0; simp at this; exact le_trans (norm_nonneg _) this
  calc ‖e n‖ * ‖gammaRPowKernel d (((n : ℝ) + 1) * y)‖
      ≤ (C * ((n : ℝ) + 1) ^ A) * (K * (((n : ℝ) + 1) ^ (-c) * y ^ (-c))) :=
        mul_le_mul (he n) h1 (norm_nonneg _) (by positivity)
    _ = C * K * y ^ (-c) * ((n : ℝ) + 1) ^ (A - c) := by
        rw [Real.rpow_sub hn, Real.rpow_neg hn.le]; field_simp

/-- **Claim 0 with root number `-1`, for `Γℝ(s)^{d+1}`.** -/
theorem gammaRPow_theta_converse_odd (d : ℕ) {e : ℕ → ℂ} {A C : ℝ} (hA : 0 ≤ A)
    (he : ∀ n : ℕ, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    (hanti : ∀ y : ℝ, 0 < y →
      (∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * (1 / y)))
        = -((y : ℂ) * ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y))) :
    Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) ∧
    (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) (1 - s)
      = -mellin (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) s) ∧
    (∀ s : ℂ, A + 1 < s.re →
      mellin (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)) s
        = (∑' n : ℕ, e n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * Gammaℝ s ^ (d + 1)) := by
  -- continuity on `(0, ∞)`
  have hθc : ContinuousOn (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
      (Ioi 0) := by
    intro y₀ hy₀
    have hy₀' : (0 : ℝ) < y₀ := hy₀
    set c : ℝ := max (A + 2) 1 with hc
    have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨K, hK⟩ := exists_norm_gammaRPowKernel_le d hc0
    have hK0 : 0 ≤ K := by
      have := hK 1 one_pos; rw [Real.one_rpow, mul_one] at this; exact le_trans (norm_nonneg _) this
    have hC0 : 0 ≤ C := by
      have := he 0; simp at this; exact le_trans (norm_nonneg _) this
    set a := y₀ / 2 with ha
    have ha0 : 0 < a := by positivity
    have hon : ContinuousOn (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
        (Ici a) := by
      refine continuousOn_tsum (u := fun n : ℕ => C * K * a ^ (-c) * ((n : ℝ) + 1) ^ (A - c))
        (f := fun (n : ℕ) (y : ℝ) => e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
        (fun n => ?_) ?_ (fun n y hy => ?_)
      · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        refine ContinuousOn.mul continuousOn_const ?_
        have hlin : ContinuousOn (fun y : ℝ => ((n : ℝ) + 1) * y) (Ici a) :=
          (continuous_const.mul continuous_id).continuousOn
        refine (continuousOn_gammaRPowKernel d).comp hlin (fun y hy => ?_)
        exact mul_pos hn (lt_of_lt_of_le ha0 hy)
      · exact (summable_succ_rpow (by rw [hc]; have := le_max_left (A + 2) 1; linarith)).mul_left _
      · have hy' : 0 < y := lt_of_lt_of_le ha0 hy
        refine (norm_theta_term_le d hc0 he hK n hy').trans ?_
        have hyc : y ^ (-c) ≤ a ^ (-c) :=
          Real.rpow_le_rpow_of_nonpos ha0 hy (by linarith)
        have hnn : 0 ≤ ((n : ℝ) + 1) ^ (A - c) := by positivity
        have hCK : 0 ≤ C * K := mul_nonneg hC0 hK0
        calc C * K * y ^ (-c) * ((n : ℝ) + 1) ^ (A - c)
            ≤ C * K * a ^ (-c) * ((n : ℝ) + 1) ^ (A - c) := by gcongr
          _ = _ := rfl
    have hnhds : Ici a ∈ 𝓝 y₀ := Ici_mem_nhds (by rw [ha]; linarith)
    exact (hon.continuousAt hnhds).continuousWithinAt
  -- rapid decay at infinity
  have hθdec : ∀ a : ℝ, (fun y : ℝ => ∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y))
      =O[atTop] fun x : ℝ => x ^ (-a) := by
    intro a
    set c : ℝ := max (A + 2) (max a 1) with hc
    have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
    have hca : a ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
    obtain ⟨K, hK⟩ := exists_norm_gammaRPowKernel_le d hc0
    have hsum := summable_succ_rpow (p := A - c) (by have := le_max_left (A + 2) (max a 1); linarith)
    rw [Asymptotics.isBigO_iff]
    refine ⟨C * K * ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c), ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hbound := tsum_of_norm_bounded ((hsum.mul_left (C * K * y ^ (-c))).hasSum)
      (fun n => norm_theta_term_le d hc0 he hK n hy0)
    rw [tsum_mul_left] at hbound
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
    have hyc : y ^ (-c) ≤ y ^ (-a) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    have hS : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c) := tsum_nonneg (fun n => by positivity)
    have hK0 : 0 ≤ K := by
      have := hK 1 one_pos; rw [Real.one_rpow, mul_one] at this; exact le_trans (norm_nonneg _) this
    have hC0 : 0 ≤ C := by
      have := he 0; simp at this; exact le_trans (norm_nonneg _) this
    calc ‖∑' n : ℕ, e n * gammaRPowKernel d (((n : ℝ) + 1) * y)‖
        ≤ C * K * y ^ (-c) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c) := hbound
      _ ≤ C * K * y ^ (-a) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c) := by gcongr
      _ = C * K * (∑' n : ℕ, ((n : ℝ) + 1) ^ (A - c)) * y ^ (-a) := by ring
  obtain ⟨h1, h2, h3⟩ := hecke_theta_converse_odd (continuousOn_gammaRPowKernel d) he hθc hθdec hanti
  refine ⟨h1, h2, fun s hs => ?_⟩
  have hs0 : 0 < s.re := by linarith
  have hmel := hasMellin_gammaRPowKernel d hs0
  have hKint : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖gammaRPowKernel d t‖) (Ioi 0) :=
    integrableOn_rpow_mul_norm_of_mellinConvergent
      (hasMellin_gammaRPowKernel d (s := ((s.re : ℝ) : ℂ)) (by simpa using hs0)).1
  rw [h3 s hs hKint, hmel.2]

end RHTower


open Complex MeasureTheory Filter Set Topology


namespace RHTower.GammaRPowTwins

open GaloisForLFunctions.HTGeometry

private theorem norm_cpow_neg_le_auxP {x : ℝ} (hx : 0 < x) {c₁ c₂ : ℝ} {s : ℂ}
    (hs : s.re ∈ uIcc c₁ c₂) : ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-c₁) + x ^ (-c₂) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [neg_re]
  rcases le_total 1 x with h1 | h1
  · rcases le_total c₁ c₂ with hc | hc
    · rw [Set.uIcc_of_le hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₁) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hs.1])
      linarith [Real.rpow_nonneg hx.le (-c₂)]
    · rw [Set.uIcc_of_ge hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₂) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hs.1])
      linarith [Real.rpow_nonneg hx.le (-c₁)]
  · rcases le_total c₁ c₂ with hc | hc
    · rw [Set.uIcc_of_le hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₂) :=
        Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hs.2])
      linarith [Real.rpow_nonneg hx.le (-c₁)]
    · rw [Set.uIcc_of_ge hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₁) :=
        Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hs.2])
      linarith [Real.rpow_nonneg hx.le (-c₂)]

/-- The Mellin symbol `Γℝ(s)^{k+1} (y^{-s} + y^{s-1})` of `K_k(y·) + y⁻¹ K_k(·/y)`. -/
def thetaSymbolPlus (k : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  Gammaℝ s ^ (k + 1) * ((y : ℂ) ^ (-s) + (y : ℂ) ^ (s - 1))

/-- The symmetric theta test function `K_k(y x) + y⁻¹ K_k(x/y)`. -/
def thetaFunctionPlus (k : ℕ) (y : ℝ) (x : ℝ) : ℂ :=
  gammaRPowKernel k (y * x) + ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel k (y⁻¹ * x)

/-- The symmetric theta symbols are regular on `0 < Re s < 1`. -/
theorem mellinRegularStrip_thetaSymbolPlus (k : ℕ) {y : ℝ} (hy : 0 < y) :
    MellinRegularStrip (thetaSymbolPlus k y) 0 1 := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  refine ⟨fun s h0 _ => ?_, fun a b ha hb K => ?_⟩
  · exact ((differentiableAt_gammaR_of_re_pos h0).pow (k + 1)).mul
      ((differentiableAt_id.neg.const_cpow (Or.inl hy0)).add
        ((differentiableAt_id.sub_const 1).const_cpow (Or.inl hy0)))
  · by_cases hab : a ≤ b
    · obtain ⟨C, hC⟩ := exists_bound_norm_gammaR_pow_strip ha hab (k + 1) K (by omega)
      set L := (y ^ (-a) + y ^ (-b)) + (y ^ (-(1 - a)) + y ^ (-(1 - b))) with hL
      refine ⟨C * L, fun s hsa hsb => ?_⟩
      have hmem : s.re ∈ uIcc a b := by rw [Set.uIcc_of_le hab]; exact ⟨hsa, hsb⟩
      have hmem' : (1 - s).re ∈ uIcc (1 - a) (1 - b) := by
        rw [Set.uIcc_of_ge (by linarith)]; simp only [sub_re, one_re]; constructor <;> linarith
      have hP : ‖(y : ℂ) ^ (-s) + (y : ℂ) ^ (s - 1)‖ ≤ L := by
        refine (norm_add_le _ _).trans (add_le_add (norm_cpow_neg_le_auxP hy hmem) ?_)
        have := norm_cpow_neg_le_auxP hy hmem'
        rwa [show -(1 - s) = s - 1 by ring] at this
      have hG := hC s hsa hsb
      have hC0 : 0 ≤ C := by
        have h0 := (norm_nonneg _).trans hG
        have hD : 0 < (1 + s.im ^ 2) ^ K := by positivity
        have := mul_nonneg h0 hD.le
        rwa [div_mul_cancel₀ _ hD.ne'] at this
      unfold thetaSymbolPlus
      rw [norm_mul]
      calc ‖Gammaℝ s ^ (k + 1)‖ * ‖(y : ℂ) ^ (-s) + (y : ℂ) ^ (s - 1)‖
          ≤ (C / (1 + s.im ^ 2) ^ K) * L := mul_le_mul hG hP (norm_nonneg _) (by positivity)
        _ = C * L / (1 + s.im ^ 2) ^ K := by ring
    · exact ⟨0, fun s hsa hsb => absurd (le_trans hsa hsb) hab⟩

/-- Symmetry: `Ψ(s) = (Γℝ(s)/Γℝ(1-s))^{k+1} Ψ(1-s)` for `Re s < 1`. -/
theorem thetaSymbolPlus_symm (k : ℕ) {y : ℝ} (s : ℂ) (h1 : s.re < 1) :
    thetaSymbolPlus k y s = (Gammaℝ s ^ (k + 1) / Gammaℝ (1 - s) ^ (k + 1)) * thetaSymbolPlus k y (1 - s) := by
  have hne : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  unfold thetaSymbolPlus
  rw [show -(1 - s) = s - 1 by ring, show 1 - s - 1 = -s by ring]
  field_simp
  ring

private theorem mellinConvergent_scaledP (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => gammaRPowKernel k (y * x)) s :=
  (MellinConvergent.comp_mul_left hy).mpr (hasMellin_gammaRPowKernel k hs).1

private theorem mellinConvergent_thetaP (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (thetaFunctionPlus k y) s := by
  have h1 := mellinConvergent_scaledP k hy hs
  have h2 := (mellinConvergent_scaledP k (inv_pos.mpr hy) hs).const_smul ((y⁻¹ : ℝ) : ℂ)
  unfold MellinConvergent at h1 h2 ⊢
  have := h1.add h2
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, thetaFunctionPlus, smul_eq_mul]
  ring

theorem mellin_thetaFunctionPlus (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    mellin (thetaFunctionPlus k y) s = thetaSymbolPlus k y s := by
  have h1 := mellinConvergent_scaledP k hy hs
  have h2 := (mellinConvergent_scaledP k (inv_pos.mpr hy) hs).const_smul ((y⁻¹ : ℝ) : ℂ)
  have hsplit : mellin (thetaFunctionPlus k y) s
      = mellin (fun x : ℝ => gammaRPowKernel k (y * x)) s
        + mellin (fun x : ℝ => ((y⁻¹ : ℝ) : ℂ) • gammaRPowKernel k (y⁻¹ * x)) s := by
    unfold mellin
    rw [← integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [thetaFunctionPlus, smul_eq_mul]; ring
  rw [hsplit, mellin_const_smul, mellin_comp_mul_left _ _ hy,
    mellin_comp_mul_left _ _ (inv_pos.mpr hy), (hasMellin_gammaRPowKernel k hs).2]
  unfold thetaSymbolPlus
  have hyarg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [smul_eq_mul, Complex.ofReal_inv]
  rw [Complex.inv_cpow _ _ hyarg, ← Complex.cpow_neg, neg_neg]
  have : (y : ℂ) ^ (s - 1) = (y : ℂ)⁻¹ * (y : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ hy0, Complex.cpow_one]; ring
  rw [this]; ring

/-- Mellin inversion for the theta test functions on every line `0 < c < 1`. -/
theorem mellinInv_thetaSymbolPlus (k : ℕ) {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {x : ℝ} (hx : 0 < x) : mellinInv c (thetaSymbolPlus k y) x = thetaFunctionPlus k y x := by
  have hreg := mellinRegularStrip_thetaSymbolPlus k hy
  have hcre : 0 < ((c : ℂ)).re := by simpa using hc
  have hconv := mellinConvergent_thetaP k hy hcre
  have hvert : VerticalIntegrable (mellin (thetaFunctionPlus k y)) c := by
    unfold VerticalIntegrable
    refine (hreg.integrable_line hc hc1).congr (Eventually.of_forall fun t => ?_)
    show thetaSymbolPlus k y ((c : ℂ) + t * I) = mellin (thetaFunctionPlus k y) ((c : ℂ) + t * I)
    rw [mellin_thetaFunctionPlus k hy (s := (c : ℂ) + t * I) (by simpa using hc)]
  have hcontx : ContinuousAt (thetaFunctionPlus k y) x := by
    unfold thetaFunctionPlus
    have h1 : ContinuousAt (fun x : ℝ => gammaRPowKernel k (y * x)) x :=
      ((continuousOn_gammaRPowKernel k).continuousAt (Ioi_mem_nhds (mul_pos hy hx))).comp
        (by fun_prop)
    have h2 : ContinuousAt (fun x : ℝ => gammaRPowKernel k (y⁻¹ * x)) x :=
      ((continuousOn_gammaRPowKernel k).continuousAt
        (Ioi_mem_nhds (mul_pos (inv_pos.mpr hy) hx))).comp (by fun_prop)
    exact h1.add (continuousAt_const.mul h2)
  have hinv := mellinInv_mellin_eq c (thetaFunctionPlus k y) hx hconv hvert hcontx
  rw [← hinv]
  unfold mellinInv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show (x : ℂ) ^ (-((c : ℂ) + t * I)) • thetaSymbolPlus k y ((c : ℂ) + t * I)
    = (x : ℂ) ^ (-((c : ℂ) + t * I)) • mellin (thetaFunctionPlus k y) ((c : ℂ) + t * I)
  rw [mellin_thetaFunctionPlus k hy (s := (c : ℂ) + t * I) (by simpa using hc)]




theorem chartSymbol_symm (d : ℕ) (hd : d ≠ 0) {Ψ : ℂ → ℂ} {w : ℂ}
    (hΨ : Ψ (chartArg d w) = (Gammaℝ (chartArg d w) ^ d / Gammaℝ (1 - chartArg d w) ^ d)
      * Ψ (1 - chartArg d w)) :
    chartSymbol d Ψ w = chartMultiplier d w * chartSymbol d Ψ (1 - w) := by
  unfold chartSymbol chartMultiplier
  rw [chartArg_one_sub d hd, hΨ]; ring

/-- Symmetric degree-`d` chart functions: `F = Mellin⁻¹_{1/2} Φ` on `(0,∞)` with `Φ` regular on
`-1 < Re w < 2` and `Φ(w) = m_d(w) Φ(1-w)`. -/
def IsSymChart (d : ℕ) (F : ℝ → ℂ) : Prop :=
  ∃ Φ : ℂ → ℂ, MellinRegularStrip Φ (-1) 2 ∧
    (∀ w : ℂ, -1 < w.re → w.re < 2 → Φ w = chartMultiplier d w * Φ (1 - w)) ∧
    ∀ X : ℝ, 0 < X → F X = mellinInv (1 / 2) Φ X

/-- The space of rapidly decaying symmetric degree-`d` chart functions. -/
def symChartSpace (d : ℕ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {F | IsSymChart d F ∧ RapidDecay F}
  zero_mem' := ⟨⟨fun _ => 0, MellinRegularStrip.zero, fun w _ _ => by simp,
    fun X _ => by simp [mellinInv]⟩, fun N => ⟨0, fun X _ => by simp⟩⟩
  add_mem' := by
    rintro F G ⟨⟨Φ, hΦ, haΦ, hFΦ⟩, hdF⟩ ⟨⟨Γ, hΓ, haΓ, hGΓ⟩, hdG⟩
    refine ⟨⟨fun s => Φ s + Γ s, hΦ.add hΓ, fun w h1 h2 => ?_, fun X hX => ?_⟩, fun N => ?_⟩
    · simp only [haΦ w h1 h2, haΓ w h1 h2]; ring
    · rw [mellinInv_add hΦ hΓ (by norm_num) (by norm_num) hX, Pi.add_apply, hFΦ X hX, hGΓ X hX]
    · obtain ⟨C₁, hC₁⟩ := hdF N
      obtain ⟨C₂, hC₂⟩ := hdG N
      refine ⟨C₁ + C₂, fun X hX => ?_⟩
      calc ‖(F + G) X‖ ≤ ‖F X‖ + ‖G X‖ := norm_add_le _ _
        _ ≤ C₁ * X ^ (-(N : ℝ)) + C₂ * X ^ (-(N : ℝ)) := add_le_add (hC₁ X hX) (hC₂ X hX)
        _ = (C₁ + C₂) * X ^ (-(N : ℝ)) := by ring
  smul_mem' := by
    rintro c F ⟨⟨Φ, hΦ, haΦ, hFΦ⟩, hdF⟩
    refine ⟨⟨fun s => c * Φ s, hΦ.const_mul c, fun w h1 h2 => ?_, fun X hX => ?_⟩, fun N => ?_⟩
    · simp only [haΦ w h1 h2]; ring
    · rw [mellinInv_const_mul, Pi.smul_apply, smul_eq_mul, hFΦ X hX]
    · obtain ⟨C, hC⟩ := hdF N
      refine ⟨‖c‖ * C, fun X hX => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC X hX) (norm_nonneg c)

/-- **Analytic package.** `F' = X⁻¹ Mellin⁻¹(-wΦ)` is the derivative of `F` on `(0,∞)` and is
continuous there; `X²|F|²` and `|F'|²` are integrable; `∫|F'|² ≤ K²∫X²|F|²`. -/
theorem IsSymChart.analytic {d : ℕ} {K : ℝ}
    (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I)‖ ≤ K)
    {F : ℝ → ℂ} (hF : IsSymChart d F) :
    ∃ F' : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt F (F' x) x) ∧ ContinuousOn F' (Ioi 0) ∧
      IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2 := by
  obtain ⟨Φ, hΦ, hanti, hFeq⟩ := hF
  have hG : MellinRegularStrip (fun w => -w * Φ w) (-1) 2 := by
    have h := (hΦ.mul_id).const_mul (-1)
    have e : (fun s => -1 * (s * Φ s)) = fun w => -w * Φ w := by funext s; ring
    rwa [e] at h
  refine ⟨fun x => ((x : ℂ))⁻¹ * mellinInv (1 / 2) (fun w => -w * Φ w) x, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := hΦ.hasDerivAt_mellinInv (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num) hx
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hFeq y hy
  · intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h := (hG.hasDerivAt_mellinInv (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      hx').continuousAt
    have hinv : ContinuousAt (fun x : ℝ => ((x : ℂ))⁻¹) x :=
      (Complex.continuous_ofReal.continuousAt).inv₀ (by exact_mod_cast hx'.ne')
    exact (hinv.mul h).continuousWithinAt
  · have h := integrableOn_norm_sq_mellinInv (Ψ := Φ) (σ := 3 / 2)
      (hΦ.integrable_line (c := 3 / 2) (by norm_num) (by norm_num))
      (hΦ.memLp_two_line (c := 3 / 2) (by norm_num) (by norm_num))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    beta_reduce
    rw [hFeq x hx', hΦ.mellinInv_eq (c₁ := 1 / 2) (c₂ := 3 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hx', show 2 * (3 / 2 : ℝ) - 1 = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
    ring
  · have h := integrableOn_norm_sq_mellinInv (Ψ := fun w => -w * Φ w) (σ := -1 / 2)
      (hG.integrable_line (c := -1 / 2) (by norm_num) (by norm_num))
      (hG.memLp_two_line (c := -1 / 2) (by norm_num) (by norm_num))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    beta_reduce
    rw [hG.mellinInv_eq (c₁ := -1 / 2) (c₂ := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hx', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx', mul_pow, show 2 * (-1 / 2 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx'.le]
    norm_cast
    ring
  · have h := integral_norm_sq_deriv_le_of_antisymm (fun w => -chartMultiplier d w) hΦ
      (fun w h1 h2 => by rw [hanti w h1 h2]; ring) (fun t => by simpa [mul_neg, norm_neg] using hK t)
    have e : ∫ x in Ioi (0 : ℝ), x ^ 2 * ‖F x‖ ^ 2
        = ∫ x in Ioi (0 : ℝ), ‖mellinInv (1 / 2) Φ x‖ ^ 2 * x ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [hFeq x hx]; ring
    rw [e]
    exact h

/-- The degree-`(k+1)` charts of the theta test functions `K_k(yx) - y⁻¹K_k(x/y)` belong to the
antisymmetric chart space (`k ≥ 2`). -/
theorem chartFun_thetaFunctionPlus_mem {k : ℕ} (hk : 2 ≤ k) {y : ℝ} (hy : 0 < y) :
    chartFun (k + 1) (thetaFunctionPlus k y) ∈ symChartSpace (k + 1) := by
  have hd : 3 ≤ k + 1 := by omega
  have hd0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  refine ⟨⟨chartSymbol (k + 1) (thetaSymbolPlus k y),
    mellinRegularStrip_chartSymbol hd (mellinRegularStrip_thetaSymbolPlus k hy),
    fun w h1 h2 => chartSymbol_symm (k + 1) (by omega)
      (thetaSymbolPlus_symm k _ (by
        rw [re_chartArg, div_lt_one hd0]
        have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [this]
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith)),
    fun X hX => ?_⟩, fun N => ?_⟩
  · rw [mellinInv_chartSymbol (by omega) _ hX]
    unfold chartFun
    rw [mellinInv_thetaSymbolPlus k hy (by norm_num) (by norm_num) (pow_pos hX _)]
  · set d : ℕ := k + 1 with hdd
    set c : ℝ := ((N : ℝ) + ((d : ℝ) - 1) / 2) / d with hc
    have hc0 : 0 < c := by
      rw [hc]; apply div_pos _ hd0
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    obtain ⟨C, hC⟩ := exists_norm_gammaRPowKernel_le k hc0
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 1 one_pos)
      simpa using this
    set D : ℝ := Real.sqrt d * (C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c))) with hD
    refine ⟨D, fun X hX => ?_⟩
    have hX0 : 0 < X := by linarith
    have hx : 0 < X ^ d := pow_pos hX0 d
    have hth : ‖thetaFunctionPlus k y (X ^ d)‖ ≤ C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c)) * (X ^ d) ^ (-c) := by
      unfold thetaFunctionPlus
      have h1 := hC (y * X ^ d) (mul_pos hy hx)
      have h2 := hC (y⁻¹ * X ^ d) (mul_pos (inv_pos.mpr hy) hx)
      rw [Real.mul_rpow hy.le hx.le] at h1
      rw [Real.mul_rpow (inv_pos.mpr hy).le hx.le] at h2
      calc ‖gammaRPowKernel k (y * X ^ d) + ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel k (y⁻¹ * X ^ d)‖
          ≤ ‖gammaRPowKernel k (y * X ^ d)‖ + y⁻¹ * ‖gammaRPowKernel k (y⁻¹ * X ^ d)‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy)]
        _ ≤ C * (y ^ (-c) * (X ^ d) ^ (-c)) + y⁻¹ * (C * (y⁻¹ ^ (-c) * (X ^ d) ^ (-c))) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hy).le)
        _ = _ := by ring
    have hpow : X ^ (((d : ℝ) - 1) / 2) * (X ^ d) ^ (-c) = X ^ (-(N : ℝ)) := by
      rw [← Real.rpow_natCast X d, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
      congr 1; rw [hc]; field_simp; ring
    unfold chartFun
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt d * X ^ (((d : ℝ) - 1) / 2))]
    calc Real.sqrt d * X ^ (((d : ℝ) - 1) / 2) * ‖thetaFunctionPlus k y (X ^ d)‖
        ≤ Real.sqrt d * X ^ (((d : ℝ) - 1) / 2) *
            (C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c)) * (X ^ d) ^ (-c)) :=
          mul_le_mul_of_nonneg_left hth (by positivity)
      _ = D * (X ^ (((d : ℝ) - 1) / 2) * (X ^ d) ^ (-c)) := by rw [hD]; ring
      _ = D * X ^ (-(N : ℝ)) := by rw [hpow]


/-- **Block relation for the symmetric chart space (degree `d ≥ 3`).** For `m+1` chart points `X_{d_i}` (`d_i ≥ 1`) a nontrivial
combination `Σ t_i F(X_{d_i})` equals a combination of the values at the integer nodes `X_{N₀+2k}`
alone, for every `F` in the antisymmetric chart space. -/
theorem exists_block_relation_sym {d : ℕ} (hd : 3 ≤ d) {K a : ℝ} {N₀ m : ℕ} (hN₀ : 1 ≤ N₀)
    (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I)‖ ≤ K)
    (hgap : ∀ j, max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| *
      (nodeSeq d N₀ m (j + 1) - nodeSeq d N₀ m j) ≤ a / 2)
    (hbr : 0 < 1 - ((1 + 1) ^ 2 * (a / (2 * Real.pi)) ^ 2 + 2 * nodeSeq d N₀ m 0 ^ 4) * K ^ 2)
    (δ : Fin (m + 1) → ℕ) (hδ : ∀ i, 1 ≤ δ i) :
    ∃ t : Fin (m + 1) → ℂ, ∃ Γ : ℕ → ℂ, ∃ A : ℝ, (∃ i, t i ≠ 0) ∧
      (∀ j, ‖Γ j‖ ≤ A * (nodeSeq d N₀ m (j + 1) + 1)) ∧
      ∀ F ∈ symChartSpace d, Summable (fun k => Γ (k + m) * F (nodeX d (N₀ + 2 * k))) ∧
        ∑ i, t i * F (nodeX d (δ i)) = ∑' k, Γ (k + m) * F (nodeX d (N₀ + 2 * k)) := by
  set p := nodeSeq d N₀ m with hpdef
  have hE : ∀ F ∈ symChartSpace d, ∃ F' : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt F (F' x) x) ∧
      ContinuousOn F' (Ioi 0) ∧ IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2 :=
    fun F hF => hF.1.analytic hK
  have hsum : ∀ F ∈ symChartSpace d, Summable fun j => max |p j| |p (j + 1)| *
      (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2) :=
    fun F hF => summable_nodeSeq_of_rapidDecay hd hF.2 hN₀ m
  have hrel : ∀ i : Fin (m + 1), ∃ γ : ℕ → ℂ, ∃ M : ℝ, (∀ j, ‖γ j‖ ^ 2 ≤ M * (p (j + 1) + 1)) ∧
      ∀ F ∈ symChartSpace d, Summable (fun j => γ j * F (p j)) ∧
        F (nodeX d (δ i)) = ∑' j, γ j * F (p j) :=
    fun i => GaloisForLFunctions.HTGeometry.exists_sampling_relation (symChartSpace d) hE
      (nodeSeq_strictMono (by omega) hN₀ m) (nodeSeq_pos (by omega) hN₀ m 0)
      (tendsto_nodeSeq (by omega) N₀ m) one_pos hgap hbr hsum (nodeX_pos (by omega) (hδ i))
  choose γ M hγ hγrel using hrel
  obtain ⟨t, ht, hkill⟩ := exists_eliminating_combination γ
  set Γ : ℕ → ℂ := fun j => ∑ i, t i * γ i j with hΓ
  refine ⟨t, Γ, ∑ i, ‖t i‖ * (|M i| + 2), ht, fun j => ?_, fun F hF => ?_⟩
  · have hp1 : 0 ≤ p (j + 1) := (nodeSeq_pos (by omega) hN₀ m _).le
    calc ‖Γ j‖ ≤ ∑ i, ‖t i * γ i j‖ := norm_sum_le _ _
      _ = ∑ i, ‖t i‖ * ‖γ i j‖ := by simp_rw [norm_mul]
      _ ≤ ∑ i, ‖t i‖ * ((|M i| + 2) * (p (j + 1) + 1)) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 := hγ i j
          have h2 : ‖γ i j‖ ≤ ‖γ i j‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖γ i j‖ - 1)]
          have h3 : M i * (p (j + 1) + 1) ≤ |M i| * (p (j + 1) + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
          nlinarith [abs_nonneg (M i)]
      _ = (∑ i, ‖t i‖ * (|M i| + 2)) * (p (j + 1) + 1) := by
          rw [Finset.sum_mul]; congr 1; funext i; ring
  · have hsumi : ∀ i, Summable fun j => t i * (γ i j * F (p j)) :=
      fun i => ((hγrel i F hF).1).mul_left (t i)
    have hsumΓ : Summable fun j => Γ j * F (p j) := by
      have := summable_sum (s := Finset.univ) (fun i _ => hsumi i)
      refine this.congr fun j => ?_
      simp only [hΓ, Finset.sum_mul]; congr 1; funext i; ring
    have hmain : ∑ i, t i * F (nodeX d (δ i)) = ∑' j, Γ j * F (p j) := by
      calc ∑ i, t i * F (nodeX d (δ i)) = ∑ i, ∑' j, t i * (γ i j * F (p j)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [(hγrel i F hF).2, ((hγrel i F hF).1).tsum_mul_left]
        _ = ∑' j, ∑ i, t i * (γ i j * F (p j)) :=
            (Summable.tsum_finsetSum (fun i _ => hsumi i)).symm
        _ = ∑' j, Γ j * F (p j) := by
            congr 1; funext j; simp only [hΓ, Finset.sum_mul]; congr 1; funext i; ring
    have hzero : ∑ j ∈ Finset.range m, Γ j * F (p j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hΓ, hkill j hj, zero_mul]
    have hsplit := hsumΓ.sum_add_tsum_nat_add m
    rw [hzero, zero_add] at hsplit
    have hshift : (fun k => Γ (k + m) * F (p (k + m)))
        = fun k => Γ (k + m) * F (nodeX d (N₀ + 2 * k)) := by
      funext k; rw [hpdef, nodeSeq_add]
    refine ⟨?_, ?_⟩
    · rw [← hshift]; exact (summable_nat_add_iff m).mpr hsumΓ
    · rw [hmain, ← hsplit, hshift]

/-- The block coefficients annihilate every symmetric theta test function. -/
theorem blockCoeff_thetaPlus_relation {k : ℕ} (hk : 2 ≤ k) {N₀ m : ℕ} (δ : Fin (m + 1) → ℕ)
    (t : Fin (m + 1) → ℂ) (Γ : ℕ → ℂ)
    (hrel : ∀ F ∈ symChartSpace (k + 1),
      Summable (fun j => Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j))) ∧
        ∑ i, t i * F (nodeX (k + 1) (δ i)) = ∑' j, Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j)))
    {y : ℝ} (hy : 0 < y) :
    Summable (fun n => blockCoeff (k + 1) N₀ m δ t Γ n * thetaFunctionPlus k y n) ∧
      ∑' n, blockCoeff (k + 1) N₀ m δ t Γ n * thetaFunctionPlus k y n = 0 := by
  obtain ⟨hs, heq⟩ := hrel _ (chartFun_thetaFunctionPlus_mem hk hy)
  simp_rw [chartFun_nodeX (by omega : 1 ≤ k + 1)] at hs heq
  set h : ℕ → ℂ := fun n => thetaFunctionPlus k y n with hh
  obtain ⟨hsum, htsum⟩ := tsum_blockCoeff_mul (d := k + 1) (N₀ := N₀) δ t Γ h hs
  exact ⟨hsum, by rw [htsum, sub_eq_zero]; exact heq⟩

/-- **Infinitely many odd theta relations for `Γ_ℝ(s)^{k+1}`, `k ≥ 2`, vanishing below `N`.** -/
theorem gammaRPow_odd_theta_relations_vanishing_below {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r, (∀ n, n + 1 < N → e r n = 0) ∧ ∃ C : ℝ,
      (∀ n, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ (k + 2)) ∧
      ∀ y : ℝ, 0 < y → (∑' n, e r n * gammaRPowKernel k (((n : ℝ) + 1) * (1 / y)))
        = -((y : ℂ) * ∑' n, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) := by
  have hd : 3 ≤ k + 1 := by omega
  obtain ⟨K, a, N₀, m, hN₀, hNN₀, -, hK, hgap, hbr⟩ := exists_chart_sampling_parameters hd N
  set δ : ℕ → Fin (m + 1) → ℕ := fun r i => N₀ + 2 * ((m + 1) * r + i) + 1 with hδ
  have hblock : ∀ r, ∃ t : Fin (m + 1) → ℂ, ∃ Γ : ℕ → ℂ, ∃ A : ℝ, (∃ i, t i ≠ 0) ∧
      (∀ j, ‖Γ j‖ ≤ A * (nodeSeq (k + 1) N₀ m (j + 1) + 1)) ∧
      ∀ F ∈ symChartSpace (k + 1), Summable (fun j => Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j))) ∧
        ∑ i, t i * F (nodeX (k + 1) (δ r i)) = ∑' j, Γ (j + m) * F (nodeX (k + 1) (N₀ + 2 * j)) :=
    fun r => exists_block_relation_sym hd hN₀ hK hgap hbr (δ r) (fun i => by simp only [hδ]; omega)
  choose t Γ A ht hΓ hrel using hblock
  set a' : ℕ → ℕ → ℂ := fun r n => blockCoeff (k + 1) N₀ m (δ r) (t r) (Γ r) n with ha'
  have ha0 : ∀ r, a' r 0 = 0 := by
    intro r
    simp only [ha', blockCoeff]
    rw [if_neg (by omega)]
    simp only [sub_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by simp only [hδ]; omega)]
  refine ⟨fun r n => a' r (n + 1), ?_, fun r => ?_⟩
  · rw [linearIndependent_iff']
    intro sfin g hg r hr
    obtain ⟨i, hi⟩ := ht r
    have hval : ∀ r', a' r' (δ r i) = if r' = r then t r i * (nodeWeight (k + 1) (δ r i) : ℂ) else 0 := by
      intro r'
      simp only [ha', blockCoeff]
      rw [if_neg (by simp only [hδ]; omega), sub_zero]
      split_ifs with hrr
      · subst hrr
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro i' _ hne
          rw [if_neg]
          intro heq
          simp only [hδ] at heq
          exact hne (skipped_index_inj heq).2.symm
        · simp
      · refine Finset.sum_eq_zero fun i' _ => ?_
        rw [if_neg]
        intro heq
        simp only [hδ] at heq
        exact hrr (skipped_index_inj heq).1.symm
    have hn : δ r i = (δ r i - 1) + 1 := by simp only [hδ]; omega
    have hev := congrFun hg (δ r i - 1)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
    rw [← hn] at hev
    simp_rw [hval] at hev
    rw [Finset.sum_eq_single r (fun r' _ hne => by rw [if_neg hne, mul_zero])
      (fun h => absurd hr h), if_pos rfl] at hev
    have hW : (nodeWeight (k + 1) (δ r i) : ℂ) ≠ 0 := by
      have h1 : 0 < nodeX (k + 1) (δ r i) := nodeX_pos (by omega) (by simp only [hδ]; omega)
      have : 0 < nodeWeight (k + 1) (δ r i) := by unfold nodeWeight; positivity
      exact_mod_cast this.ne'
    rcases mul_eq_zero.mp hev with h | h
    · exact h
    · exact absurd h (mul_ne_zero hi hW)
  · have hlow : ∀ n, n + 1 < N → a' r (n + 1) = 0 := by
      intro n hn
      simp only [ha', blockCoeff]
      rw [if_neg (by omega), sub_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (by simp only [hδ]; omega)]
    refine ⟨hlow, ?_⟩
    set C₀ := (∑ i, ‖t r i‖ + 5 * |A r|) * (Real.sqrt ((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1)) with hC₀
    have hC₀0 : 0 ≤ C₀ := by
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (t r i))
      have := abs_nonneg (A r); positivity
    have hgrowth : ∀ n, ‖a' r (n + 1)‖ ≤ 2 ^ (k + 2) * C₀ * ((n : ℝ) + 1) ^ (k + 2) := by
      intro n
      have h := norm_blockCoeff_le hd hN₀ (δ r) (t r) (hΓ r) (n + 1)
      refine h.trans ?_
      have hb : (((n + 1 : ℕ) : ℝ) + 1) ^ (k + 1 + 1) ≤ 2 ^ (k + 2) * ((n : ℝ) + 1) ^ (k + 2) := by
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have := mul_le_mul_of_nonneg_left hb hC₀0
      calc C₀ * (((n + 1 : ℕ) : ℝ) + 1) ^ (k + 1 + 1) ≤ C₀ * (2 ^ (k + 2) * ((n : ℝ) + 1) ^ (k + 2)) :=
            this
        _ = 2 ^ (k + 2) * C₀ * ((n : ℝ) + 1) ^ (k + 2) := by ring
    refine ⟨2 ^ (k + 2) * C₀, hgrowth, fun y hy => ?_⟩
    obtain ⟨hsum, hzero⟩ := blockCoeff_thetaPlus_relation hk (δ r) (t r) (Γ r) (hrel r) hy
    have hshift := hsum.tsum_eq_zero_add
    rw [hzero] at hshift
    have h0 : a' r 0 * thetaFunctionPlus k y ((0 : ℕ) : ℝ) = 0 := by rw [ha0 r, zero_mul]
    simp only [ha'] at h0
    rw [h0, zero_add] at hshift
    have hy' : 0 < y⁻¹ := inv_pos.mpr hy
    have hs1 := summable_mul_gammaRPowKernel k (k + 2) hgrowth hy
    have hs2 := summable_mul_gammaRPowKernel k (k + 2) hgrowth hy'
    have hexp : (fun n : ℕ => blockCoeff (k + 1) N₀ m (δ r) (t r) (Γ r) (n + 1) *
        thetaFunctionPlus k y ((n + 1 : ℕ) : ℝ)) = fun n =>
        a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * y) +
          ((y⁻¹ : ℝ) : ℂ) * (a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * y⁻¹)) := by
      funext n
      simp only [ha', thetaFunctionPlus]
      push_cast
      ring_nf
    rw [hexp, hs1.tsum_add (hs2.mul_left _), hs2.tsum_mul_left] at hshift
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hfin := eq_neg_of_add_eq_zero_left hshift.symm
    rw [show (fun n : ℕ => a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * (1 / y)))
        = fun n => a' r (n + 1) * gammaRPowKernel k (((n : ℝ) + 1) * y⁻¹) by
      funext n; rw [one_div]]
    rw [hfin]
    push_cast
    field_simp


/-- **Odd functional equations of `Γ_ℝ(s)^d`-type have infinitely many solutions, `d ≥ 3`.** For
`d = k+1 ≥ 3` and every `N` there are linearly independent coefficient sequences `e_r`, vanishing at
all integers `< N`, such that `Γ_ℝ(s)^d Σ_n e_r(n)(n+1)^{-s}` (for `Re s > k+3`) extends to an entire
function `Λ_r` with `Λ_r(1-s) = -Λ_r(s)`. In degree 1 there are none (odd Hamburger). -/
theorem gammaRPow_odd_functional_equation_abundance {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    ∃ e : ℕ → ℕ → ℂ, LinearIndependent ℂ e ∧ ∀ r, (∀ n, n + 1 < N → e r n = 0) ∧
      Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) ∧
      (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) (1 - s)
        = -mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) s) ∧
      (∀ s : ℂ, (k : ℝ) + 3 < s.re →
        mellin (fun y : ℝ => ∑' n : ℕ, e r n * gammaRPowKernel k (((n : ℝ) + 1) * y)) s
          = (∑' n : ℕ, e r n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * Gammaℝ s ^ (k + 1)) := by
  obtain ⟨e, hind, he⟩ := gammaRPow_odd_theta_relations_vanishing_below hk N
  refine ⟨e, hind, fun r => ?_⟩
  obtain ⟨hlow, C, hC, hanti⟩ := he r
  have hC' : ∀ n : ℕ, ‖e r n‖ ≤ C * ((n : ℝ) + 1) ^ ((k + 2 : ℕ) : ℝ) := fun n => by
    rw [Real.rpow_natCast]; exact hC n
  obtain ⟨h1, h2, h3⟩ := RHTower.gammaRPow_theta_converse_odd k (by positivity) hC' hanti
  refine ⟨hlow, h1, h2, fun s hs => h3 s (by push_cast; linarith)⟩

end RHTower.GammaRPowTwins
