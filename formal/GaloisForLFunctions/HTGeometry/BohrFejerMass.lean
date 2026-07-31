import GaloisForLFunctions.HTGeometry.BohrMeanTriangle

/-!
# Mass concentration of the Fejér kernel, measured by a continuous majorant

The convergence step needs the kernel to put asymptotically all of its mass near its peaks.  Rather
than integrate against an indicator — which would leave the class of continuous almost-periodic
functions — the standard device is the continuous majorant `1 − cos(βu)`, which is bounded below by a
positive constant away from the peaks.

For the Fejér kernel the corresponding mass is computed exactly.  Its Fourier coefficient at the
frequency `±β` is the number of pairs `(a,b)` in `[0,N]²` with `a − b = ±1`, namely `N`, divided by
`N+1`; hence

`M_u( F_N(u) · (1 − cos βu) ) = 1 − N/(N+1) = 1/(N+1) → 0`.

So the mass the kernel places away from its peaks vanishes, quantitatively.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The Bohr coefficients of the Fejér kernel. -/
theorem bohrCoefficient_fejerKernel (β : ℝ) (N : ℕ) (lam : ℝ) :
    bohrCoefficient (fejerKernel β N) lam
      = ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          if ((p.1 : ℝ) - (p.2 : ℝ)) * β = lam then ((N : ℂ) + 1)⁻¹ else 0 := by
  classical
  have h : fejerKernel β N = fun u => ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
      ((N : ℂ) + 1)⁻¹ * expChar (((p.1 : ℝ) - (p.2 : ℝ)) * β) u :=
    funext fun u => fejerKernel_eq_sum β N u
  rw [h, bohrCoefficient_sum_expChar (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
    (fun _ : ℕ × ℕ => ((N : ℂ) + 1)⁻¹)
    (fun p : ℕ × ℕ => ((p.1 : ℝ) - (p.2 : ℝ)) * β) lam]

/-- The Fejér coefficient at the frequency `β`. -/
theorem bohrCoefficient_fejerKernel_self {β : ℝ} (hβ : β ≠ 0) (N : ℕ) :
    bohrCoefficient (fejerKernel β N) β = (N : ℂ) * ((N : ℂ) + 1)⁻¹ := by
  classical
  rw [bohrCoefficient_fejerKernel, ← Finset.sum_filter]
  have hinj : Function.Injective (fun b : ℕ => ((b + 1, b) : ℕ × ℕ)) := by
    intro a b hab
    exact congrArg Prod.snd hab
  have hfilter :
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          fun p => ((p.1 : ℝ) - (p.2 : ℝ)) * β = β)
        = (Finset.range N).image (fun b : ℕ => ((b + 1, b) : ℕ × ℕ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hcond⟩
      have hd : (p.1 : ℝ) - (p.2 : ℝ) = 1 := by
        have h1β : ((p.1 : ℝ) - (p.2 : ℝ)) * β = 1 * β := by rw [hcond, one_mul]
        exact mul_right_cancel₀ hβ h1β
      have hnat : p.1 = p.2 + 1 := by
        have : (p.1 : ℝ) = (p.2 : ℝ) + 1 := by linarith
        exact_mod_cast this
      refine ⟨p.2, by omega, ?_⟩
      rw [← hnat]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      push_cast
      ring
  rw [hfilter, Finset.sum_const, Finset.card_image_of_injective _ hinj, Finset.card_range,
    nsmul_eq_mul]

/-- The Fejér coefficient at the frequency `−β`. -/
theorem bohrCoefficient_fejerKernel_neg {β : ℝ} (hβ : β ≠ 0) (N : ℕ) :
    bohrCoefficient (fejerKernel β N) (-β) = (N : ℂ) * ((N : ℂ) + 1)⁻¹ := by
  classical
  rw [bohrCoefficient_fejerKernel, ← Finset.sum_filter]
  have hinj : Function.Injective (fun a : ℕ => ((a, a + 1) : ℕ × ℕ)) := by
    intro a b hab
    exact congrArg Prod.fst hab
  have hfilter :
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          fun p => ((p.1 : ℝ) - (p.2 : ℝ)) * β = -β)
        = (Finset.range N).image (fun a : ℕ => ((a, a + 1) : ℕ × ℕ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hcond⟩
      have hd : (p.1 : ℝ) - (p.2 : ℝ) = -1 := by
        have h1β : ((p.1 : ℝ) - (p.2 : ℝ)) * β = (-1) * β := by rw [hcond]; ring
        exact mul_right_cancel₀ hβ h1β
      have hnat : p.2 = p.1 + 1 := by
        have : (p.2 : ℝ) = (p.1 : ℝ) + 1 := by linarith
        exact_mod_cast this
      refine ⟨p.1, by omega, ?_⟩
      rw [← hnat]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      push_cast
      ring
  rw [hfilter, Finset.sum_const, Finset.card_image_of_injective _ hinj, Finset.card_range,
    nsmul_eq_mul]

/-- **Mass away from the peaks.**  The Fejér kernel integrated against the continuous majorant
`1 − cos(βu)` has mean exactly `1/(N+1)`. -/
theorem bohrMean_fejerKernel_mul_one_sub_cos {β : ℝ} (hβ : β ≠ 0) (N : ℕ) :
    bohrMean (fun u => fejerKernel β N u *
        (1 - (expChar β u + expChar (-β) u) / 2))
      = ((N : ℂ) + 1)⁻¹ := by
  have hkc : Continuous (fejerKernel β N) := continuous_fejerKernel β N
  have hka : HTGeometry.IsBohrAlmostPeriodic (fejerKernel β N) := by
    have h : fejerKernel β N = fun u => ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        ((N : ℂ) + 1)⁻¹ * expChar (((p.1 : ℝ) - (p.2 : ℝ)) * β) u :=
      funext fun u => fejerKernel_eq_sum β N u
    rw [h]
    exact isBohrAlmostPeriodic_sum _ (fun p _ => continuous_const.mul (continuous_expChar _))
      (fun p _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))
  -- the three pieces
  have hsplit : (fun u => fejerKernel β N u * (1 - (expChar β u + expChar (-β) u) / 2))
      = fun u => fejerKernel β N u
        - ((2 : ℂ)⁻¹ * (fejerKernel β N u * expChar β u)
          + (2 : ℂ)⁻¹ * (fejerKernel β N u * expChar (-β) u)) := by
    funext u
    field_simp
  have hmul1 : bohrMean (fun u => fejerKernel β N u * expChar β u)
      = (N : ℂ) * ((N : ℂ) + 1)⁻¹ := by
    have hchar : (fun u => fejerKernel β N u * expChar β u)
        = fun u => fejerKernel β N u * bohrChar (-β) u :=
      funext fun u => by rw [expChar_eq_bohrChar]
    rw [hchar]
    exact bohrCoefficient_fejerKernel_neg hβ N
  have hmul2 : bohrMean (fun u => fejerKernel β N u * expChar (-β) u)
      = (N : ℂ) * ((N : ℂ) + 1)⁻¹ := by
    have hchar : (fun u => fejerKernel β N u * expChar (-β) u)
        = fun u => fejerKernel β N u * bohrChar β u := by
      funext u
      rw [expChar_eq_bohrChar]
      congr 1
      ring
    rw [hchar]
    exact bohrCoefficient_fejerKernel_self hβ N
  have hc1 : Continuous fun u => fejerKernel β N u * expChar β u :=
    hkc.mul (continuous_expChar _)
  have ha1 : HTGeometry.IsBohrAlmostPeriodic fun u => fejerKernel β N u * expChar β u :=
    isBohrAlmostPeriodic_mul hkc hka (continuous_expChar _) (isBohrAlmostPeriodic_expChar _)
  have hc2 : Continuous fun u => fejerKernel β N u * expChar (-β) u :=
    hkc.mul (continuous_expChar _)
  have ha2 : HTGeometry.IsBohrAlmostPeriodic fun u => fejerKernel β N u * expChar (-β) u :=
    isBohrAlmostPeriodic_mul hkc hka (continuous_expChar _) (isBohrAlmostPeriodic_expChar _)
  rw [hsplit,
    bohrMean_sub (f := fejerKernel β N)
      (g := fun u => (2 : ℂ)⁻¹ * (fejerKernel β N u * expChar β u)
        + (2 : ℂ)⁻¹ * (fejerKernel β N u * expChar (-β) u))
      hkc hka
      ((continuous_const.mul hc1).add (continuous_const.mul hc2))
      (isBohrAlmostPeriodic_add (continuous_const.mul hc1)
        (isBohrAlmostPeriodic_const_mul _ ha1)
        (continuous_const.mul hc2) (isBohrAlmostPeriodic_const_mul _ ha2)),
    bohrMean_add (f := fun u => (2 : ℂ)⁻¹ * (fejerKernel β N u * expChar β u))
      (g := fun u => (2 : ℂ)⁻¹ * (fejerKernel β N u * expChar (-β) u))
      (continuous_const.mul hc1) (isBohrAlmostPeriodic_const_mul _ ha1)
      (continuous_const.mul hc2) (isBohrAlmostPeriodic_const_mul _ ha2),
    bohrMean_const_mul (f := fun u => fejerKernel β N u * expChar β u) _ hc1 ha1,
    bohrMean_const_mul (f := fun u => fejerKernel β N u * expChar (-β) u) _ hc2 ha2,
    hmul1, hmul2, bohrMean_fejerKernel hβ N]
  have hne : ((N : ℂ) + 1) ≠ 0 := by
    intro hz
    have hR : ((N : ℝ) + 1) = 0 := by exact_mod_cast hz
    have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    linarith
  field_simp
  ring_nf

end

end GaloisForLFunctions
