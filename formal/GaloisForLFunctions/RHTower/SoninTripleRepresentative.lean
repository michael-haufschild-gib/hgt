import GaloisForLFunctions.RHTower.ZetaTripleTail
import GaloisForLFunctions.RHTower.ZetaDivPowRepresentative
import GaloisForLFunctions.RHTower.MellinHeadHardyEquiv

/-!
# The analytic representative of `s(s-1)ζ(s)/((s-ρ₁)(s-ρ₂)(s-ρ)^l)`

The quotient carries junk values at `1`, `ρ₁`, `ρ₂` and `ρ`; its meromorphic normal form is the
honest object, analytic on the open critical strip exactly when the multiplicity of each of the
three points in the divisor does not exceed the order of `ζ` there.

On the right half `1/2 < Re s < 1` the representative is the Hardy function of the previous file
transported by `s = w + 1/2`, hence — by Paley–Wiener — the Mellin transform of a square-integrable
tail datum with *vanishing* head constant.  That vanishing is what will put the resulting vector in
the Sonine space `K₁` rather than merely in `L₁`.

## Main results

* `soninTripleNF`, `analyticAt_soninTripleNF`
* `exists_tail_soninTripleNF`
-/

open Complex Set Filter Topology MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The raw quotient `s(s-1)ζ(s)/((s-ρ₁)(s-ρ₂)(s-ρ)^l)`. -/
def soninTriple (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) : ℂ → ℂ := fun s =>
  s * (s - 1) * riemannZeta s / ((s - ρ₁) * ((s - ρ₂) * (s - ρ) ^ l))

/-- Its analytic representative. -/
def soninTripleNF (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn (soninTriple ρ₁ ρ₂ ρ l) Set.univ

theorem analyticAt_soninTripleDenom (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (z - ρ₁) * ((z - ρ₂) * (z - ρ) ^ l)) s :=
  (analyticAt_id.sub analyticAt_const).mul
    ((analyticAt_id.sub analyticAt_const).mul (analyticAt_sub_const_pow ρ l s))

theorem meromorphicAt_soninTriple (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) (s : ℂ) :
    MeromorphicAt (soninTriple ρ₁ ρ₂ ρ l) s := by
  have hfun : soninTriple ρ₁ ρ₂ ρ l
      = (fun z : ℂ => z * (z - 1) * riemannZeta z)
        / fun z : ℂ => (z - ρ₁) * ((z - ρ₂) * (z - ρ) ^ l) := by
    funext z
    rw [soninTriple, Pi.div_apply]
  rw [hfun]
  exact MeromorphicAt.div
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).meromorphicAt.mul
      (meromorphicAt_riemannZeta_everywhere s))
    (analyticAt_soninTripleDenom ρ₁ ρ₂ ρ l s).meromorphicAt

theorem analyticAt_soninTriple {ρ₁ ρ₂ ρ : ℂ} {l : ℕ} {s : ℂ} (h1 : s ≠ 1) (hs₁ : s ≠ ρ₁)
    (hs₂ : s ≠ ρ₂) (hsρ : s ≠ ρ) : AnalyticAt ℂ (soninTriple ρ₁ ρ₂ ρ l) s := by
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using h1)
  have hden : ((s : ℂ) - ρ₁) * ((s - ρ₂) * (s - ρ) ^ l) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 hs₁)
      (mul_ne_zero (sub_ne_zero.2 hs₂) (pow_ne_zero _ (sub_ne_zero.2 hsρ)))
  exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hζ).div
    (analyticAt_soninTripleDenom ρ₁ ρ₂ ρ l s) hden

theorem meromorphicOn_soninTriple (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) :
    MeromorphicOn (soninTriple ρ₁ ρ₂ ρ l) Set.univ := fun z _ => meromorphicAt_soninTriple _ _ _ _ z

theorem meromorphicOrderAt_soninTripleNF (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) (z : ℂ) :
    meromorphicOrderAt (soninTripleNF ρ₁ ρ₂ ρ l) z
      = meromorphicOrderAt (soninTriple ρ₁ ρ₂ ρ l) z :=
  meromorphicOrderAt_congr
    ((meromorphicOn_soninTriple ρ₁ ρ₂ ρ l).toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z))

theorem soninTripleNF_eq_of_analyticAt {ρ₁ ρ₂ ρ : ℂ} {l : ℕ} {z : ℂ}
    (h : AnalyticAt ℂ (soninTriple ρ₁ ρ₂ ρ l) z) :
    soninTripleNF ρ₁ ρ₂ ρ l z = soninTriple ρ₁ ρ₂ ρ l z := by
  have hmero : MeromorphicOn (soninTriple ρ₁ ρ₂ ρ l) Set.univ := meromorphicOn_soninTriple _ _ _ _
  simp [soninTripleNF, toMeromorphicNFOn, hmero,
    ← (toMeromorphicNFAt_eq_self.2 h.meromorphicNFAt).symm]

theorem soninTripleNF_eq {ρ₁ ρ₂ ρ : ℂ} {l : ℕ} {s : ℂ} (h1 : s ≠ 1) (hs₁ : s ≠ ρ₁)
    (hs₂ : s ≠ ρ₂) (hsρ : s ≠ ρ) :
    soninTripleNF ρ₁ ρ₂ ρ l s
      = s * (s - 1) * riemannZeta s / ((s - ρ₁) * ((s - ρ₂) * (s - ρ) ^ l)) :=
  soninTripleNF_eq_of_analyticAt (analyticAt_soninTriple h1 hs₁ hs₂ hsρ)

/-! ## The order on the critical strip -/

theorem meromorphicOrderAt_id_of_ne {z : ℂ} (h0 : z ≠ 0) :
    meromorphicOrderAt (id : ℂ → ℂ) z = (0 : WithTop ℤ) := by
  have hne : (id : ℂ → ℂ) z ≠ 0 := h0
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) z := analyticAt_id
  rw [hid.meromorphicOrderAt_eq, hid.analyticOrderAt_eq_zero.2 hne]
  simp

theorem meromorphicOrderAt_soninTripleNum {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    meromorphicOrderAt (fun w : ℂ => w * (w - 1) * riemannZeta w) z
      = meromorphicOrderAt riemannZeta z := by
  have hfun : (fun w : ℂ => w * (w - 1) * riemannZeta w)
      = ((id : ℂ → ℂ) * fun w : ℂ => w - 1) * riemannZeta := by
    funext w
    rw [Pi.mul_apply, Pi.mul_apply]
    rfl
  rw [hfun, meromorphicOrderAt_mul (f := (id : ℂ → ℂ) * fun w : ℂ => w - 1) (g := riemannZeta)
      ((analyticAt_id.meromorphicAt).mul (analyticAt_id.sub analyticAt_const).meromorphicAt)
      (meromorphicAt_riemannZeta_everywhere z),
    meromorphicOrderAt_mul (f := (id : ℂ → ℂ)) (g := fun w : ℂ => w - 1)
      analyticAt_id.meromorphicAt (analyticAt_id.sub analyticAt_const).meromorphicAt,
    meromorphicOrderAt_id_of_ne h0, meromorphicOrderAt_sub_const_of_ne h1]
  simp

theorem meromorphicOrderAt_soninTripleDen (ρ₁ ρ₂ ρ : ℂ) (l : ℕ) (z : ℂ) :
    meromorphicOrderAt (fun w : ℂ => (w - ρ₁) * ((w - ρ₂) * (w - ρ) ^ l)) z
      = ((((if z = ρ₁ then (1 : ℤ) else 0) + ((if z = ρ₂ then (1 : ℤ) else 0)
          + (l : ℤ) * (if z = ρ then (1 : ℤ) else 0))) : ℤ) : WithTop ℤ) := by
  classical
  have hpow : meromorphicOrderAt (fun w : ℂ => (w - ρ) ^ l) z
      = ((((l : ℤ) * (if z = ρ then (1 : ℤ) else 0)) : ℤ) : WithTop ℤ) := by
    by_cases h : z = ρ
    · rw [if_pos h, h, meromorphicOrderAt_sub_pow]
      norm_num
    · rw [if_neg h, meromorphicOrderAt_sub_pow_of_ne l h]
      norm_num
  have hfun : (fun w : ℂ => (w - ρ₁) * ((w - ρ₂) * (w - ρ) ^ l))
      = (fun w : ℂ => w - ρ₁) * ((fun w : ℂ => w - ρ₂) * fun w : ℂ => (w - ρ) ^ l) := by
    funext w
    rw [Pi.mul_apply, Pi.mul_apply]
  rw [hfun, meromorphicOrderAt_mul (f := fun w : ℂ => w - ρ₁)
      (g := (fun w : ℂ => w - ρ₂) * fun w : ℂ => (w - ρ) ^ l)
      (analyticAt_id.sub analyticAt_const).meromorphicAt
      (((analyticAt_id.sub analyticAt_const).meromorphicAt).mul
        (analyticAt_sub_const_pow ρ l z).meromorphicAt),
    meromorphicOrderAt_mul (f := fun w : ℂ => w - ρ₂) (g := fun w : ℂ => (w - ρ) ^ l)
      (analyticAt_id.sub analyticAt_const).meromorphicAt
      (analyticAt_sub_const_pow ρ l z).meromorphicAt,
    meromorphicOrderAt_sub_point, meromorphicOrderAt_sub_point, hpow]
  norm_cast

theorem meromorphicOrderAt_soninTriple {ρ₁ ρ₂ ρ : ℂ} {l : ℕ} {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    meromorphicOrderAt (soninTriple ρ₁ ρ₂ ρ l) z
      = meromorphicOrderAt riemannZeta z
        - ((((if z = ρ₁ then (1 : ℤ) else 0) + ((if z = ρ₂ then (1 : ℤ) else 0)
          + (l : ℤ) * (if z = ρ then (1 : ℤ) else 0))) : ℤ) : WithTop ℤ) := by
  have hfun : soninTriple ρ₁ ρ₂ ρ l
      = (fun w : ℂ => w * (w - 1) * riemannZeta w)
        / fun w : ℂ => (w - ρ₁) * ((w - ρ₂) * (w - ρ) ^ l) := by
    funext w
    rw [soninTriple, Pi.div_apply]
  rw [hfun, meromorphicOrderAt_div (f := fun w : ℂ => w * (w - 1) * riemannZeta w)
      (g := fun w : ℂ => (w - ρ₁) * ((w - ρ₂) * (w - ρ) ^ l))
      ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).meromorphicAt.mul
        (meromorphicAt_riemannZeta_everywhere z))
      (analyticAt_soninTripleDenom ρ₁ ρ₂ ρ l z).meromorphicAt,
    meromorphicOrderAt_soninTripleNum h0 h1, meromorphicOrderAt_soninTripleDen]

/-- **The representative is analytic on the strip** as soon as the divisor multiplicities do not
exceed the orders of `ζ`. -/
theorem analyticAt_soninTripleNF {ρ₁ ρ₂ ρ : ℂ} {l : ℕ} {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1)
    (hcnt : (((if z = ρ₁ then (1 : ℤ) else 0) + ((if z = ρ₂ then (1 : ℤ) else 0)
          + (l : ℤ) * (if z = ρ then (1 : ℤ) else 0))) : WithTop ℤ)
        ≤ meromorphicOrderAt riemannZeta z) :
    AnalyticAt ℂ (soninTripleNF ρ₁ ρ₂ ρ l) z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at h0; norm_num at h0
  have hz1 : z ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  have hNF : MeromorphicNFAt (soninTripleNF ρ₁ ρ₂ ρ l) z :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ z)
  refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
  rw [meromorphicOrderAt_soninTripleNF, meromorphicOrderAt_soninTriple hz0 hz1]
  exact withTop_sub_nonneg_of_le hcnt

/-! ## The pure tail datum -/

/-- **The representative is the Mellin transform of a square-integrable tail** at aperture one,
with vanishing head constant. -/
theorem exists_tail_soninTripleNF {ρ₁ ρ₂ ρ : ℂ} {l m₁ m₂ mρ : ℕ}
    (hρ₁0 : ρ₁ ≠ 0) (hρ₁1 : ρ₁ ≠ 1) (hρ₂0 : ρ₂ ≠ 0) (hρ₂1 : ρ₂ ≠ 1)
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hl : 1 ≤ l)
    (hm₁ : (m₁ : ℕ∞) ≤ analyticOrderAt riemannZeta ρ₁)
    (hm₂ : (m₂ : ℕ∞) ≤ analyticOrderAt riemannZeta ρ₂)
    (hmρ : (mρ : ℕ∞) ≤ analyticOrderAt riemannZeta ρ)
    (hb₀ : (l : ℤ) + (if ρ₂ = ρ then 1 else 0) + (if ρ₁ = ρ then 1 else 0) ≤ (mρ : ℤ))
    (hb₁ : (if ρ = ρ₁ then (l : ℤ) else 0) + (if ρ₂ = ρ₁ then 1 else 0) + 1 ≤ (m₁ : ℤ))
    (hb₂ : (if ρ = ρ₂ then (l : ℤ) else 0) + 1 + (if ρ₁ = ρ₂ then 1 else 0) ≤ (m₂ : ℤ))
    (hana : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 → AnalyticAt ℂ (soninTripleNF ρ₁ ρ₂ ρ l) z) :
    ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioi (1 : ℝ))) ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        soninTripleNF ρ₁ ρ₂ ρ l s = headTailMellin 1 0 g s := by
  classical
  obtain ⟨K, MK, hK, hKval⟩ := exists_isHalfPlaneHardy_zetaTriple hρ₁0 hρ₁1 hρ₂0 hρ₂1 hρ0 hρ1 hl
    hm₁ hm₂ hmρ hb₀ hb₁ hb₂
  set F : ℂ → ℂ := fun s => K (s - 1 / 2) with hFdef
  have hFtail : IsMellinTailHardy 1 F := by
    refine ⟨MK, ?_⟩
    have hfun : (fun w : ℂ => (((1 : ℝ)) : ℂ) ^ w * F (w + 1 / 2)) = K := by
      funext w
      rw [Complex.ofReal_one, Complex.one_cpow, one_mul, hFdef]
      show K (w + 1 / 2 - 1 / 2) = K w
      congr 1
      ring
    rw [hfun]
    exact hK
  obtain ⟨g, hg, hgeq⟩ := (isMellinTailHardy_iff one_pos F).1 hFtail
  -- the representative agrees with the Hardy transport away from the three divisor points
  have hoff : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → s ≠ ρ → s ≠ ρ₁ → s ≠ ρ₂ →
      soninTripleNF ρ₁ ρ₂ ρ l s = F s := by
    intro s hs1 hs2 hsρ hs₁ hs₂
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs1; norm_num at hs1
    have hsone : s ≠ 1 := by intro h; rw [h] at hs2; norm_num at hs2
    have hw : (s : ℂ) - 1 / 2 ≠ -(1 / 2) := by
      intro h; exact hs0 (by linear_combination h)
    have hwhalf : (s : ℂ) - 1 / 2 ≠ 1 / 2 := by
      intro h; exact hsone (by linear_combination h)
    have hwρ : (s : ℂ) - 1 / 2 ≠ ρ - 1 / 2 := by
      intro h; exact hsρ (by linear_combination h)
    have hw₁ : (s : ℂ) - 1 / 2 ≠ ρ₁ - 1 / 2 := by
      intro h; exact hs₁ (by linear_combination h)
    have hw₂ : (s : ℂ) - 1 / 2 ≠ ρ₂ - 1 / 2 := by
      intro h; exact hs₂ (by linear_combination h)
    have hden : ((s : ℂ) - ρ₁) * ((s - ρ₂) * (s - ρ) ^ l) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.2 hs₁)
        (mul_ne_zero (sub_ne_zero.2 hs₂) (pow_ne_zero _ (sub_ne_zero.2 hsρ)))
    have hsq : ((s : ℂ)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hs0
    show soninTripleNF ρ₁ ρ₂ ρ l s = K (s - 1 / 2)
    rw [soninTripleNF_eq hsone hs₁ hs₂ hsρ, hKval (s - 1 / 2) hw hwρ hw₁ hw₂,
      zetaShiftCoreNF_eq hwhalf hw,
      show ((s : ℂ) - 1 / 2 - 1 / 2) = s - 1 from by ring,
      show ((s : ℂ) - 1 / 2 + 1 / 2) = s from by ring,
      show ((s : ℂ) - 1 / 2 - (ρ₁ - 1 / 2)) = s - ρ₁ from by ring,
      show ((s : ℂ) - 1 / 2 - (ρ₂ - 1 / 2)) = s - ρ₂ from by ring,
      show ((s : ℂ) - 1 / 2 - (ρ - 1 / 2)) = s - ρ from by ring]
    field_simp
  have hFeq : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → soninTripleNF ρ₁ ρ₂ ρ l s = F s := by
    intro s hs1 hs2
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : s ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := ⟨hs1, hs2⟩
    have hcont1 : ContinuousAt (soninTripleNF ρ₁ ρ₂ ρ l) s := (hana s hs1 hs2).continuousAt
    have hcont2 : ContinuousAt F s := by
      have hopenR : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
      have hre : 0 < ((s : ℂ) - 1 / 2).re := by
        simp only [Complex.sub_re]
        have hhalf : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
        rw [hhalf]
        linarith
      have hKana : AnalyticAt ℂ K (s - 1 / 2) := hK.holo.analyticAt (hopenR.mem_nhds hre)
      have hshift : ContinuousAt (fun z : ℂ => z - 1 / 2) s :=
        (continuous_id.sub continuous_const).continuousAt
      exact hKana.continuousAt.comp (x := s) hshift
    have hev : ∀ p : ℂ, ∀ᶠ z : ℂ in 𝓝[≠] s, z ≠ p := by
      intro p
      by_cases hp : s = p
      · subst hp
        filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
      · exact eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hp)
    refine eq_of_eventuallyEq_punctured hcont1 hcont2 ?_
    have h₁ : ∀ᶠ z : ℂ in 𝓝 s, z ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
      hopen.eventually_mem hmem
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁, hev ρ, hev ρ₁, hev ρ₂]
      with z hz' hzρ hz₁ hz₂
    exact hoff z hz'.1 hz'.2 hzρ hz₁ hz₂
  refine ⟨g, hg, ?_⟩
  intro s hs1 hs2
  rw [hFeq s hs1 hs2, hgeq s hs1, headTailMellin]
  simp

end

end RHTower
