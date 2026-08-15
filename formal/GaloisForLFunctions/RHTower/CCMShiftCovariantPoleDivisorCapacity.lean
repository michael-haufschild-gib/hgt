import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# Shift-covariant pole-to-divisor transport costs one norm unit per divisor copy

The Laplace transform turns the unilateral translation semigroup on `L²(0, ∞)` into multiplication
by `exp(-hz)` on the Hardy space of the right half-plane, so a translation-covariant operator taking
the incoming Euler pole vector `2e^{-t/2}` to a finite transverse divisor profile
`2 ∑ m_j e^{-λ_j t}` is multiplication by the rational symbol

`φ_D(z) = (z + 1/2) ∑ m_j / (z + λ_j)`.

Along the positive real axis `φ_D` tends to the total multiplicity `κ(D) = ∑ m_j`, so any uniform
bound on `φ_D` over the right half-plane is at least `κ(D)`.  A nonempty divisor packet closed under
conjugation and free of real points has `κ(D) ≥ 2`, so no contractive shift-covariant symbol can
carry one functional-equation pair.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-- The incoming completed Euler pole profile on the half-line. -/
def polePacketProfile (t : ℝ) : ℂ := 2 * Complex.exp (-((1 / 2 : ℂ) * (t : ℂ)))

/-- The transverse divisor profile of a finite right-half packet. -/
def divisorPacketProfile {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) (t : ℝ) : ℂ :=
  2 * ∑ j, (m j : ℂ) * Complex.exp (-(lam j * (t : ℂ)))

/-- The total multiplicity of a finite divisor packet. -/
def divisorPacketMultiplicity {r : ℕ} (m : Fin r → ℕ) : ℕ := ∑ j, m j

/-- The shift-covariant Hardy symbol taking the pole vector to the divisor profile. -/
def poleDivisorMultiplier {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) (z : ℂ) : ℂ :=
  (z + 1 / 2) * ∑ j, (m j : ℂ) / (z + lam j)

/-! ## The two Laplace transforms -/

/-- **Equation (9), pole half.**  The Laplace transform of the incoming pole profile. -/
theorem laplace_polePacketProfile {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * polePacketProfile t) = 2 / (z + 1 / 2) := by
  have hb : 0 < (z + 1 / 2).re := by
    simp only [Complex.add_re, Complex.div_re]
    norm_num
    linarith
  have hcongr : ∀ t : ℝ, Complex.exp (-(z * (t : ℂ))) * polePacketProfile t
      = 2 * Complex.exp (-((z + 1 / 2) * (t : ℂ))) := by
    intro t
    unfold polePacketProfile
    rw [← mul_assoc, mul_comm (Complex.exp (-(z * (t : ℂ)))) 2, mul_assoc, ← Complex.exp_add]
    ring_nf
  calc (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * polePacketProfile t)
      = ∫ t in Ioi (0 : ℝ), 2 * Complex.exp (-((z + 1 / 2) * (t : ℂ))) := by
        exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hcongr t
    _ = 2 * ∫ t in Ioi (0 : ℝ), Complex.exp (-((z + 1 / 2) * (t : ℂ))) := by
        rw [integral_const_mul]
    _ = 2 / (z + 1 / 2) := by
        rw [integral_Ioi_cexp_neg_mul hb]
        ring

/-- **Equation (9), divisor half.**  The Laplace transform of the divisor profile. -/
theorem laplace_divisorPacketProfile {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * divisorPacketProfile lam m t) =
      2 * ∑ j, (m j : ℂ) / (z + lam j) := by
  have hbj : ∀ j, 0 < (z + lam j).re := by
    intro j
    have := hlam j
    simp only [Complex.add_re]
    linarith
  have hcongr : ∀ t : ℝ, Complex.exp (-(z * (t : ℂ))) * divisorPacketProfile lam m t
      = ∑ j, 2 * (m j : ℂ) * Complex.exp (-((z + lam j) * (t : ℂ))) := by
    intro t
    simp only [divisorPacketProfile, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hexp : Complex.exp (-(z * (t : ℂ))) * Complex.exp (-(lam j * (t : ℂ)))
        = Complex.exp (-((z + lam j) * (t : ℂ))) := by
      rw [← Complex.exp_add]
      ring_nf
    linear_combination (2 * (m j : ℂ)) * hexp
  have hint : ∀ j : Fin r, IntegrableOn
      (fun t : ℝ => 2 * (m j : ℂ) * Complex.exp (-((z + lam j) * (t : ℂ)))) (Ioi (0 : ℝ)) volume :=
    fun j => (integrableOn_Ioi_cexp_neg_mul (hbj j)).const_mul _
  calc (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * divisorPacketProfile lam m t)
      = ∫ t in Ioi (0 : ℝ), ∑ j, 2 * (m j : ℂ) * Complex.exp (-((z + lam j) * (t : ℂ))) := by
        exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hcongr t
    _ = ∑ j, ∫ t in Ioi (0 : ℝ), 2 * (m j : ℂ) * Complex.exp (-((z + lam j) * (t : ℂ))) := by
        exact integral_finsetSum _ fun j _ => hint j
    _ = 2 * ∑ j, (m j : ℂ) / (z + lam j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, integral_Ioi_cexp_neg_mul (hbj j), div_eq_mul_inv, mul_assoc]

/-- **Equations (5), (7).**  The symbol multiplies the pole transform into the divisor transform. -/
theorem poleDivisorMultiplier_mul_pole {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) {z : ℂ}
    (hz : 0 < z.re) :
    poleDivisorMultiplier lam m z * (2 / (z + 1 / 2)) = 2 * ∑ j, (m j : ℂ) / (z + lam j) := by
  have hne : z + 1 / 2 ≠ 0 := by
    intro h
    have hre : (z + 1 / 2).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.div_re] at hre
    norm_num at hre
    linarith
  have hne2 : z * 2 + 1 ≠ 0 := by
    intro h
    apply hne
    linear_combination h / 2
  have key : (z + 1 / 2) * (2 / (z + 1 / 2)) = 2 := by field_simp
  calc poleDivisorMultiplier lam m z * (2 / (z + 1 / 2))
      = ((z + 1 / 2) * (2 / (z + 1 / 2))) * ∑ j, (m j : ℂ) / (z + lam j) := by
        unfold poleDivisorMultiplier
        ring
    _ = 2 * ∑ j, (m j : ℂ) / (z + lam j) := by rw [key]

/-! ## The real-axis limit is the total multiplicity -/

theorem tendsto_inv_add_atTop (c : ℂ) :
    Tendsto (fun x : ℝ => ((x : ℂ) + c)⁻¹) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun x : ℝ => ‖(x : ℂ) + c‖) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right atTop (-‖c‖) tendsto_id)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h1 : ‖(x : ℂ)‖ - ‖(-c)‖ ≤ ‖(x : ℂ) - (-c)‖ := norm_sub_norm_le _ _
    rw [norm_neg, sub_neg_eq_add] at h1
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] using h1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hnorm

theorem tendsto_ratio_one (c : ℂ) :
    Tendsto (fun x : ℝ => ((x : ℂ) + 1 / 2) / ((x : ℂ) + c)) atTop (𝓝 1) := by
  have hev : ∀ᶠ x : ℝ in atTop,
      ((x : ℂ) + 1 / 2) / ((x : ℂ) + c) = 1 + (1 / 2 - c) * ((x : ℂ) + c)⁻¹ := by
    filter_upwards [eventually_gt_atTop (‖c‖ + 1)] with x hx
    have hne : (x : ℂ) + c ≠ 0 := by
      intro h
      have hx0 : ‖(x : ℂ)‖ = ‖c‖ := by
        have : (x : ℂ) = -c := by linear_combination h
        rw [this, norm_neg]
      have hxpos : (0 : ℝ) ≤ x := le_of_lt (lt_of_le_of_lt (by positivity) hx)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos] at hx0
      linarith
    field_simp
    ring
  have hlim : Tendsto (fun x : ℝ => 1 + (1 / 2 - c) * ((x : ℂ) + c)⁻¹) atTop (𝓝 1) := by
    have := ((tendsto_inv_add_atTop c).const_mul ((1 : ℂ) / 2 - c)).const_add (1 : ℂ)
    simpa using this
  exact hlim.congr' (hev.mono fun x hx => hx.symm)

/-- **Equation (10).**  Along the positive real axis the shift-covariant symbol tends to the total
divisor multiplicity. -/
theorem tendsto_poleDivisorMultiplier_atTop {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) :
    Tendsto (fun x : ℝ => poleDivisorMultiplier lam m (x : ℂ)) atTop
      (𝓝 ((divisorPacketMultiplicity m : ℕ) : ℂ)) := by
  have hsum : ∀ x : ℝ, poleDivisorMultiplier lam m (x : ℂ)
      = ∑ j, (m j : ℂ) * (((x : ℂ) + 1 / 2) / ((x : ℂ) + lam j)) := by
    intro x
    unfold poleDivisorMultiplier
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlim : Tendsto (fun x : ℝ => ∑ j, (m j : ℂ) * (((x : ℂ) + 1 / 2) / ((x : ℂ) + lam j)))
      atTop (𝓝 (∑ j, (m j : ℂ) * 1)) :=
    tendsto_finsetSum _ fun j _ => (tendsto_ratio_one (lam j)).const_mul _
  have hval : (∑ j, (m j : ℂ) * 1) = ((divisorPacketMultiplicity m : ℕ) : ℂ) := by
    unfold divisorPacketMultiplicity
    push_cast
    simp
  rw [← hval]
  exact hlim.congr fun x => (hsum x).symm

/-- **Equation (6).**  Every uniform bound for the shift-covariant symbol on the right half-plane is
at least the total divisor multiplicity. -/
theorem divisorPacketMultiplicity_le_of_bound {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) {C : ℝ}
    (hC : ∀ z : ℂ, 0 < z.re → ‖poleDivisorMultiplier lam m z‖ ≤ C) :
    ((divisorPacketMultiplicity m : ℕ) : ℝ) ≤ C := by
  have hlim : Tendsto (fun x : ℝ => ‖poleDivisorMultiplier lam m (x : ℂ)‖) atTop
      (𝓝 ‖((divisorPacketMultiplicity m : ℕ) : ℂ)‖) :=
    (tendsto_poleDivisorMultiplier_atTop lam m).norm
  have hnorm : ‖((divisorPacketMultiplicity m : ℕ) : ℂ)‖
      = ((divisorPacketMultiplicity m : ℕ) : ℝ) := by
    simp
  rw [← hnorm]
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact hC (x : ℂ) (by simpa using hx)

/-! ## A conjugation-closed packet costs at least two units -/

/-- **Equation (11).**  A nonempty divisor packet closed under conjugation with no real point has
total multiplicity at least two. -/
theorem two_le_divisorPacketMultiplicity {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ)
    (hm : ∀ j, 0 < m j) (σ : Fin r → Fin r)
    (hσ : ∀ j, lam (σ j) = (starRingEnd ℂ) (lam j))
    (him : ∀ j, (lam j).im ≠ 0) (j₀ : Fin r) :
    2 ≤ divisorPacketMultiplicity m := by
  classical
  have hne : σ j₀ ≠ j₀ := by
    intro h
    have := hσ j₀
    rw [h] at this
    have him0 : (lam j₀).im = 0 := by
      have := congrArg Complex.im this
      simp at this
      linarith
    exact him j₀ him0
  have hsub : ({j₀, σ j₀} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair : ∑ j ∈ ({j₀, σ j₀} : Finset (Fin r)), m j = m j₀ + m (σ j₀) := by
    rw [Finset.sum_pair (Ne.symm hne)]
  have hle : ∑ j ∈ ({j₀, σ j₀} : Finset (Fin r)), m j ≤ divisorPacketMultiplicity m :=
    Finset.sum_le_sum_of_subset hsub
  have h1 := hm j₀
  have h2 := hm (σ j₀)
  unfold divisorPacketMultiplicity at hle ⊢
  omega

/-- **Equation (12).**  No contractive shift-covariant symbol carries a nonempty conjugation-closed
divisor packet. -/
theorem not_contractive_poleDivisorMultiplier {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ)
    (hm : ∀ j, 0 < m j) (σ : Fin r → Fin r)
    (hσ : ∀ j, lam (σ j) = (starRingEnd ℂ) (lam j))
    (him : ∀ j, (lam j).im ≠ 0) (j₀ : Fin r) :
    ¬ (∀ z : ℂ, 0 < z.re → ‖poleDivisorMultiplier lam m z‖ ≤ 1) := by
  intro hC
  have h1 := divisorPacketMultiplicity_le_of_bound lam m hC
  have h2 := two_le_divisorPacketMultiplicity lam m hm σ hσ him j₀
  have : (2 : ℝ) ≤ ((divisorPacketMultiplicity m : ℕ) : ℝ) := by exact_mod_cast h2
  linarith

/-- **The functional-equation input.**  A zeta zero in the open critical strip is not real. -/
theorem riemannZeta_zero_im_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : s.im ≠ 0 := by
  intro him
  have hs : s = ((s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hs] at hz
  exact _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo h0 h1 hz

end

end GaloisForLFunctions.RHTower
