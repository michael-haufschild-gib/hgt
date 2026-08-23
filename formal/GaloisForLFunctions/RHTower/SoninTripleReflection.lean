import GaloisForLFunctions.RHTower.SoninTripleRepresentative
import GaloisForLFunctions.RHTower.MellinReflectionEquation
import GaloisForLFunctions.RHTower.ZetaDivPowHeadTail

/-!
# The reflection of `s(s-1)ζ(s)/((s-ρ₁)(s-ρ₂)(s-ρ)^l)`

The functional equation `ζ(s) = χ(s)ζ(1-s)` turns the reflected quotient into the quotient of the
same shape at the mirror points `1-ρ₁`, `1-ρ₂`, `1-ρ`, up to the sign `(-1)^l` produced by the three
reflected linear factors.  Since `ζ` has equal orders at `ρ` and `1-ρ`, the mirror data satisfy the
same multiplicity bounds, so the reflected function is again a pure tail transform.

## Main results

* `soninTripleNF_reflect`
-/

open Complex Set Filter Topology MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The reflected quotient is the quotient at the mirror points.** -/
theorem soninTripleNF_reflect {ρ₁ ρ₂ ρ : ℂ} {l : ℕ}
    (hana : ∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ (soninTripleNF ρ₁ ρ₂ ρ l) z)
    (hana' : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF (1 - ρ₁) (1 - ρ₂) (1 - ρ) l) z) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      burnolChiFactor s * soninTripleNF ρ₁ ρ₂ ρ l (1 - s)
        = (-1 : ℂ) ^ l * soninTripleNF (1 - ρ₁) (1 - ρ₂) (1 - ρ) l s := by
  classical
  have hoff : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      s ≠ 1 - ρ₁ → s ≠ 1 - ρ₂ → s ≠ 1 - ρ →
      burnolChiFactor s * soninTripleNF ρ₁ ρ₂ ρ l (1 - s)
        = (-1 : ℂ) ^ l * soninTripleNF (1 - ρ₁) (1 - ρ₂) (1 - ρ) l s := by
    intro s hs1 hs2 h₁ h₂ hρ
    have hs0 : 0 < s.re := by linarith
    have hint : ∀ m : ℤ, s ≠ (m : ℂ) := ne_intCast_of_mem_strip hs0 hs2
    have hzeta : riemannZeta s = burnolChiFactor s * riemannZeta (1 - s) :=
      riemannZeta_eq_burnolChiFactor_mul_one_sub hint
    have hsne1 : s ≠ 1 := by simpa using hint 1
    have hsne0 : s ≠ 0 := by simpa using hint 0
    have hmone : (1 : ℂ) - s ≠ 1 := by
      intro h
      exact hsne0 (by linear_combination -h)
    have hm₁ : (1 : ℂ) - s ≠ ρ₁ := by
      intro h
      exact h₁ (by linear_combination -h)
    have hm₂ : (1 : ℂ) - s ≠ ρ₂ := by
      intro h
      exact h₂ (by linear_combination -h)
    have hmρ : (1 : ℂ) - s ≠ ρ := by
      intro h
      exact hρ (by linear_combination -h)
    rw [soninTripleNF_eq hmone hm₁ hm₂ hmρ, soninTripleNF_eq hsne1 h₁ h₂ hρ]
    have hsign : ((1 : ℂ) - s - ρ) ^ l = (-1 : ℂ) ^ l * (s - (1 - ρ)) ^ l := by
      rw [show ((1 : ℂ) - s - ρ) = -(s - (1 - ρ)) from by ring, neg_pow]
    have hd₁ : ((1 : ℂ) - s - ρ₁) = -(s - (1 - ρ₁)) := by ring
    have hd₂ : ((1 : ℂ) - s - ρ₂) = -(s - (1 - ρ₂)) := by ring
    have hsq : ((-1 : ℂ)) ^ l * ((-1 : ℂ)) ^ l = 1 := by
      rw [← mul_pow]
      norm_num
    have hinv : (((-1 : ℂ)) ^ l)⁻¹ = ((-1 : ℂ)) ^ l := inv_eq_of_mul_eq_one_right hsq
    have hden : ((1 : ℂ) - s - ρ₁) * (((1 : ℂ) - s - ρ₂) * ((1 : ℂ) - s - ρ) ^ l)
        = (-1 : ℂ) ^ l * ((s - (1 - ρ₁)) * ((s - (1 - ρ₂)) * (s - (1 - ρ)) ^ l)) := by
      rw [hd₁, hd₂, hsign]
      ring
    rw [hden, hzeta]
    simp only [div_eq_mul_inv, mul_inv]
    rw [hinv]
    ring
  intro s hs1 hs2
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : s ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := ⟨hs1, hs2⟩
  have hcont1 : ContinuousAt
      (fun z : ℂ => burnolChiFactor z * soninTripleNF ρ₁ ρ₂ ρ l (1 - z)) s := by
    have hchi : ContinuousAt burnolChiFactor s := (differentiableAt_burnolChiFactor hs2).continuousAt
    have hre1 : 0 < ((1 : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hre2 : ((1 : ℂ) - s).re < 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hNF : ContinuousAt (soninTripleNF ρ₁ ρ₂ ρ l) (1 - s) :=
      (hana (1 - s) hre1 hre2).continuousAt
    have hshift : ContinuousAt (fun z : ℂ => 1 - z) s :=
      (continuous_const.sub continuous_id).continuousAt
    exact hchi.mul (hNF.comp (x := s) hshift)
  have hcont2 : ContinuousAt
      (fun z : ℂ => (-1 : ℂ) ^ l * soninTripleNF (1 - ρ₁) (1 - ρ₂) (1 - ρ) l z) s :=
    continuousAt_const.mul (hana' s hs1 hs2).continuousAt
  have hev : ∀ p : ℂ, ∀ᶠ z : ℂ in 𝓝[≠] s, z ≠ p := by
    intro p
    by_cases hp : s = p
    · subst hp
      filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
    · exact eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hp)
  refine eq_of_eventuallyEq_punctured hcont1 hcont2 ?_
  have h₁ : ∀ᶠ z : ℂ in 𝓝 s, z ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := hopen.eventually_mem hmem
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁, hev (1 - ρ₁), hev (1 - ρ₂),
    hev (1 - ρ)] with z hz' hz₁ hz₂ hzρ
  exact hoff z hz'.1 hz'.2 hz₁ hz₂ hzρ

end

end RHTower
