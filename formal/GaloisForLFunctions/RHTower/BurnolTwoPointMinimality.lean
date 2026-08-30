import GaloisForLFunctions.RHTower.BurnolMinimalitySystem
import GaloisForLFunctions.RHTower.SoninTripleReflection
import GaloisForLFunctions.RHTower.SoninCarrierFromExtended

/-!
# The two-omission Sonine carrier

Burnol's Proposition 6.5 has a minimality half in addition to its already-formalized completeness
half.  Its source vectors have completed Mellin transforms

`s(s - 1) ζ(s) / ((s - rho1) (s - rho2) (s - rho)^l)`.

The three quotient factors consume exactly the two omitted top-order jets and the selected jet.
This module proves the hard carrier realization: whenever the literal divisor budgets make the
triple quotient and its reflection pure Hardy tails, they produce a literal vector of `K_1`, with
both aperture constants zero and with that exact completed Mellin transform on the whole critical
strip.

This is an unconditional source theorem.  It does not assert RH or claim the final
minimality-system assembly; it supplies the missing `L_1 -> K_1` realization needed by that
assembly.
-/

open Complex Set Filter Topology MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A two-sided pure-tail completed Mellin datum for a triple quotient produces an actual
Sonine vector at aperture one, not merely an extended-Sonine vector. -/
theorem exists_centralSonin_soninTriple_of_twoSidedTail
    {rho1 rho2 rho : ℂ} {l : ℕ}
    (hana : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF rho1 rho2 rho l) z)
    {gRight : ℝ → ℂ} (hgRight : MemLp gRight 2 (volume.restrict (Ioi (1 : ℝ))))
    (hRight : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      soninTripleNF rho1 rho2 rho l s = headTailMellin 1 0 gRight s)
    {gLeft : ℝ → ℂ} (hgLeft : MemLp gLeft 2 (volume.restrict (Ioi (1 : ℝ))))
    (hLeft : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      burnolChiFactor s * soninTripleNF rho1 rho2 rho l (1 - s) =
        headTailMellin 1 0 gLeft s) :
    ∃ v : SoninL2, v ∈ evenSubspace ∧ v ∈ centralSoninCarrier 1 ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0) ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s := by
  obtain ⟨_, hFour⟩ := headTailVector_mem_centralSoninExtendedCarrier one_pos
    (fun z hz => (hana z hz.1 hz.2).continuousAt.continuousWithinAt)
    hgRight hRight hgLeft hLeft
  let v : SoninL2 := headTailVector one_pos 0 hgRight
  have hEven : v ∈ evenSubspace := headTailVector_mem_evenSubspace one_pos 0 hgRight
  have hPhys : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0 := by
    simpa [v] using (headTailVector_ae_band one_pos (0 : ℂ) hgRight)
  have hFour' : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0 := by
    simpa [v] using hFour
  have hCarrier : v ∈ centralSoninCarrier 1 :=
    mem_centralSoninCarrier_of_ae_zero hPhys hFour'
  refine ⟨v, hEven, hCarrier, hFour', hPhys, ?_⟩
  have hRightMellin : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s := by
    intro s hs1 hs2
    have hsne : s ≠ 1 := by
      intro hs
      rw [hs] at hs2
      norm_num at hs2
    rw [extendedMellinContinuation_headTailVector one_pos 0 hgRight hFour' hs1 hsne,
      ← hRight s hs1 hs2]
  intro s hs0 hs1
  have hAnalyticV : AnalyticOnNhd ℂ (extendedMellinContinuation 1 0 0 v)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp at hz
    exact analyticAt_extendedMellinContinuation_of_ne one_pos hEven hFour' hPhys hz0 hz1
  have hAnalyticF : AnalyticOnNhd ℂ (soninTripleNF rho1 rho2 rho l)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    exact hana z hz.1 hz.2
  have hSeed : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    constructor
    · norm_num
    · norm_num
  have hEqNear : extendedMellinContinuation 1 0 0 v =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)]
      soninTripleNF rho1 rho2 rho l := by
    have hRightOpen : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := isOpen_rightStrip
    have hMem : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := by
      constructor
      · norm_num
      · norm_num
    filter_upwards [hRightOpen.mem_nhds hMem] with z hz
    exact hRightMellin z hz.1 hz.2
  exact hAnalyticV.eqOn_of_preconnected_of_eventuallyEq hAnalyticF
    isPreconnected_criticalOpenStrip hSeed hEqNear ⟨hs0, hs1⟩

/-- Exact jet-order transport for a realized triple quotient.  This is the algebraic bridge from
the `K₁` carrier to the shortened evaluator system: the two omitted jets and the selected jet are
subtracted with their literal multiplicities at every critical-strip point. -/
theorem meromorphicOrderAt_extendedMellin_soninTriple_of_eq
    {v : SoninL2} {rho1 rho2 rho : ℂ} {l : ℕ}
    (hMellin : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    meromorphicOrderAt (extendedMellinContinuation 1 0 0 v) z =
      meromorphicOrderAt riemannZeta z
        - ((((if z = rho1 then (1 : ℤ) else 0) + ((if z = rho2 then (1 : ℤ) else 0)
          + (l : ℤ) * (if z = rho then (1 : ℤ) else 0))) : ℤ) : WithTop ℤ) := by
  have hloc : extendedMellinContinuation 1 0 0 v =ᶠ[𝓝 z] soninTripleNF rho1 rho2 rho l := by
    filter_upwards [isOpen_openStrip.mem_nhds
      (show z ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} from ⟨hz0, hz1⟩)] with s hs
    exact hMellin s hs.1 hs.2
  have hz0' : z ≠ 0 := by
    intro hz
    rw [hz] at hz0
    norm_num at hz0
  have hz1' : z ≠ 1 := by
    intro hz
    rw [hz] at hz1
    norm_num at hz1
  rw [meromorphicOrderAt_congr (hloc.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_soninTripleNF,
    meromorphicOrderAt_soninTriple hz0' hz1']

/-- At each point of the open critical strip, the meromorphic and natural analytic zeta
multiplicities agree exactly.  This removes the only coercion ambiguity in the finite-defect
two-omission system. -/
theorem meromorphicOrderAt_riemannZeta_eq_toNat_of_strip {z : ℂ}
    (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    meromorphicOrderAt riemannZeta z =
      (((analyticOrderAt riemannZeta z).toNat : ℤ) : WithTop ℤ) := by
  have hfin : analyticOrderAt riemannZeta z ≠ ⊤ :=
    analyticOrderAt_riemannZeta_ne_top_of_strip hz0 hz1
  have htoNat : ((analyticOrderAt riemannZeta z).toNat : ℕ∞) =
      analyticOrderAt riemannZeta z := ENat.coe_toNat hfin
  have hz1' : z ≠ 1 := by
    intro hz
    rw [hz] at hz1
    norm_num at hz1
  have hana : AnalyticAt ℂ riemannZeta z :=
    analyticOn_riemannZeta z (by simpa using hz1')
  rw [hana.meromorphicOrderAt_eq, ← htoNat]
  simp

/-- Multiplicity removed by omitting the two top evaluator jets. -/
def twoPointOmissionOrder (rho1 rho2 z : ℂ) : WithTop ℤ :=
  (((if z = rho1 then (1 : ℤ) else 0) + (if z = rho2 then (1 : ℤ) else 0) : ℤ) : WithTop ℤ)

/-- Natural multiplicity removed by omitting the two named top evaluator jets. -/
def twoPointOmissionMultiplicity (rho1 rho2 z : ℂ) : ℕ :=
  (if z = rho1 then 1 else 0) + (if z = rho2 then 1 else 0)

/-- Finite multiplicity of the zeta divisor at a critical-strip point. Strip hypotheses supply
the finiteness whenever this number is used. -/
def zetaStripMultiplicity (z : ℂ) : ℕ := (analyticOrderAt riemannZeta z).toNat

private theorem twoPoint_triple_budget_of_retained_jet
    {rho1 rho2 rho : ℂ} {m : ℂ → ℕ} {k : ℕ}
    (hselected : k < m rho - twoPointOmissionMultiplicity rho1 rho2 rho)
    (h1 : twoPointOmissionMultiplicity rho1 rho2 rho1 ≤ m rho1)
    (h2 : twoPointOmissionMultiplicity rho1 rho2 rho2 ≤ m rho2)
    {z : ℂ} (hz : z = rho ∨ z = rho1 ∨ z = rho2) :
    twoPointOmissionMultiplicity rho1 rho2 z +
      (if z = rho then m rho - twoPointOmissionMultiplicity rho1 rho2 rho - k else 0) ≤ m z := by
  rcases hz with hzr | hzr | hzr
  · subst z
    simp only [if_pos]
    omega
  · subst z
    by_cases h : rho1 = rho
    · subst rho1
      simp only [if_pos]
      omega
    · have h' : rho ≠ rho1 := Ne.symm h
      simp [twoPointOmissionMultiplicity, h]
      simpa [twoPointOmissionMultiplicity] using h1
  · subst z
    by_cases h : rho2 = rho
    · subst rho2
      simp only [if_pos]
      omega
    · have h' : rho ≠ rho2 := Ne.symm h
      simp [twoPointOmissionMultiplicity, h]
      simpa [twoPointOmissionMultiplicity] using h2

private theorem twoPoint_literal_triple_budgets_of_retained_jet
    {rho1 rho2 rho : ℂ} {m : ℂ → ℕ} {k : ℕ}
    (hselected : k < m rho - twoPointOmissionMultiplicity rho1 rho2 rho)
    (h1 : twoPointOmissionMultiplicity rho1 rho2 rho1 ≤ m rho1)
    (h2 : twoPointOmissionMultiplicity rho1 rho2 rho2 ≤ m rho2) :
    (m rho - twoPointOmissionMultiplicity rho1 rho2 rho - k)
        + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ m rho ∧
      (if rho = rho1 then m rho - twoPointOmissionMultiplicity rho1 rho2 rho - k else 0)
        + (if rho2 = rho1 then 1 else 0) + 1 ≤ m rho1 ∧
      (if rho = rho2 then m rho - twoPointOmissionMultiplicity rho1 rho2 rho - k else 0)
        + 1 + (if rho1 = rho2 then 1 else 0) ≤ m rho2 := by
  by_cases h12 : rho1 = rho2
  · subst rho2
    by_cases h : rho = rho1
    · subst rho
      simp [twoPointOmissionMultiplicity] at hselected h1 h2 ⊢
      omega
    · have h' : rho1 ≠ rho := Ne.symm h
      simp [twoPointOmissionMultiplicity, h, h'] at hselected h1 h2 ⊢
      omega
  · by_cases h1rho : rho = rho1
    · subst rho
      have h12' : rho2 ≠ rho1 := Ne.symm h12
      simp [twoPointOmissionMultiplicity, h12, h12'] at hselected h1 h2 ⊢
      omega
    · by_cases h2rho : rho = rho2
      · subst rho
        have h12' : rho2 ≠ rho1 := Ne.symm h12
        simp [twoPointOmissionMultiplicity, h12, h12'] at hselected h1 h2 ⊢
        omega
      · have h1rho' : rho1 ≠ rho := Ne.symm h1rho
        have h2rho' : rho2 ≠ rho := Ne.symm h2rho
        have h12' : rho2 ≠ rho1 := Ne.symm h12
        simp [twoPointOmissionMultiplicity, h12, h12', h1rho, h1rho', h2rho, h2rho'] at hselected h1 h2 ⊢
        omega

private theorem twoPoint_triple_divisor_count_eq_omission_add
    (rho1 rho2 rho : ℂ) (l : ℕ) :
    ((↑(if rho = rho1 then (1 : ℤ) else 0) : WithTop ℤ) +
      ((↑(if rho = rho2 then (1 : ℤ) else 0) : WithTop ℤ) +
        (↑(l : ℤ) : WithTop ℤ) * ↑(if rho = rho then (1 : ℤ) else 0))) =
      ((↑(twoPointOmissionMultiplicity rho1 rho2 rho : ℤ) : WithTop ℤ) +
        ((l : ℤ) : WithTop ℤ)) := by
  have homega : ((↑(twoPointOmissionMultiplicity rho1 rho2 rho : ℤ) : WithTop ℤ) =
      (↑(if rho = rho1 then (1 : ℤ) else 0) : WithTop ℤ) +
        (↑(if rho = rho2 then (1 : ℤ) else 0) : WithTop ℤ)) := by
    simp [twoPointOmissionMultiplicity]
  rw [homega]
  simp only [if_pos]
  ac_rfl

private theorem twoPoint_retained_order_sub_omission_eq
    {m d k : ℕ} (hselected : k < m - d) :
    ((m : ℤ) : WithTop ℤ) -
        (((d : ℤ) : WithTop ℤ) + (((m - d - k : ℕ) : ℤ) : WithTop ℤ)) =
      ((k : ℤ) : WithTop ℤ) := by
  have hdle : d ≤ m := by omega
  have hkle : k ≤ m - d := by omega
  have hcast : ((m - d - k : ℕ) : ℤ) = (m : ℤ) - (d : ℤ) - (k : ℤ) := by
    rw [Nat.cast_sub hkle, Nat.cast_sub hdle]
  have hsel : (k : ℤ) < (m : ℤ) - (d : ℤ) := by
    rw [← Nat.cast_sub hdle]
    exact_mod_cast hselected
  have hint : (m : ℤ) - ((d : ℤ) + ((m - d - k : ℕ) : ℤ)) = (k : ℤ) := by
    rw [hcast]
    omega
  exact_mod_cast hint

/-- A literal `K₁` witness for one retained jet after the two top jets at `rho1`, `rho2` have
been omitted. -/
def IsTwoPointOmittedEvaluatorWitness (rho1 rho2 rho : ℂ) (k : ℕ) (v : SoninL2) : Prop :=
  v ∈ evenSubspace ∧ v ∈ centralSoninCarrier 1 ∧
    (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0) ∧
    (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0) ∧
    (∀ z : ℂ, 0 < z.re → z.re < 1 → z ≠ rho →
      meromorphicOrderAt (extendedMellinContinuation 1 0 0 v) z =
        meromorphicOrderAt riemannZeta z - twoPointOmissionOrder rho1 rho2 z) ∧
    meromorphicOrderAt (extendedMellinContinuation 1 0 0 v) rho = ((k : ℤ) : WithTop ℤ)

/-- An exact triple quotient is a finite-defect shortened-evaluator witness as soon as its
selected order is the retained jet order. -/
theorem isTwoPointOmittedEvaluatorWitness_of_exactMellin
    {rho1 rho2 rho : ℂ} {l k : ℕ} {v : SoninL2}
    (hev : v ∈ evenSubspace) (hK : v ∈ centralSoninCarrier 1)
    (hFour : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0)
    (hPhys : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0)
    (hMellin : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s)
    (htarget : meromorphicOrderAt (extendedMellinContinuation 1 0 0 v) rho =
      ((k : ℤ) : WithTop ℤ)) :
    IsTwoPointOmittedEvaluatorWitness rho1 rho2 rho k v := by
  refine ⟨hev, hK, hFour, hPhys, ?_, htarget⟩
  intro z hz0 hz1 hne
  rw [meromorphicOrderAt_extendedMellin_soninTriple_of_eq hMellin hz0 hz1]
  simp [twoPointOmissionOrder, hne]

/-- The three literal divisor budgets already force regularity of the triple quotient throughout
the critical strip.  Thus analyticity in the two-omission carrier is a consequence of source
multiplicity data, not an extra analytic certificate. -/
private theorem soninTriple_count_le_of_budget_at_rho
    {rho1 rho2 rho : ℂ} {l mr : ℕ} {M : WithTop ℤ}
    (hb0 : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ (mr : ℤ))
    (hmr : ((mr : ℤ) : WithTop ℤ) ≤ M) :
    ((↑(if rho = rho1 then (1 : ℤ) else 0) : WithTop ℤ) +
      ((↑(if rho = rho2 then (1 : ℤ) else 0) : WithTop ℤ) +
        (↑(l : ℤ) : WithTop ℤ) * ↑(if rho = rho then (1 : ℤ) else 0))) ≤ M := by
  have hbudget : ((↑(l : ℤ) : WithTop ℤ) +
      (↑(if rho2 = rho then (1 : ℤ) else 0) : WithTop ℤ) +
      (↑(if rho1 = rho then (1 : ℤ) else 0) : WithTop ℤ)) ≤ M := by
    exact le_trans (by exact_mod_cast hb0) hmr
  rcases eq_or_ne rho1 rho with h1 | h1 <;> rcases eq_or_ne rho2 rho with h2 | h2
  · subst rho1
    subst rho2
    norm_num at hbudget ⊢
    calc
      1 + (1 + (↑(l : ℤ) : WithTop ℤ)) =
          (↑(l : ℤ) : WithTop ℤ) + 1 + 1 := by ac_rfl
      _ ≤ M := hbudget
  · subst rho1
    have h2' : rho ≠ rho2 := Ne.symm h2
    simp [h2, h2'] at hbudget ⊢
    calc
      1 + (↑(l : ℤ) : WithTop ℤ) = (↑(l : ℤ) : WithTop ℤ) + 1 := by ac_rfl
      _ ≤ M := hbudget
  · subst rho2
    have h1' : rho ≠ rho1 := Ne.symm h1
    simp [h1, h1'] at hbudget ⊢
    calc
      1 + (↑(l : ℤ) : WithTop ℤ) = (↑(l : ℤ) : WithTop ℤ) + 1 := by ac_rfl
      _ ≤ M := hbudget
  · have h1' : rho ≠ rho1 := Ne.symm h1
    have h2' : rho ≠ rho2 := Ne.symm h2
    simp [h1, h1', h2, h2'] at hbudget ⊢
    exact hbudget

private theorem soninTriple_count_le_of_budget_at_rho1
    {rho1 rho2 rho : ℂ} {l m1 : ℕ} {M : WithTop ℤ}
    (hnot : rho1 ≠ rho)
    (hb1 : (if rho = rho1 then (l : ℤ) else 0) +
      (if rho2 = rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hm1 : ((m1 : ℤ) : WithTop ℤ) ≤ M) :
    ((↑(if rho1 = rho1 then (1 : ℤ) else 0) : WithTop ℤ) +
      ((↑(if rho1 = rho2 then (1 : ℤ) else 0) : WithTop ℤ) +
        (↑(l : ℤ) : WithTop ℤ) * ↑(if rho1 = rho then (1 : ℤ) else 0))) ≤ M := by
  have hbudget : ((↑(if rho = rho1 then (l : ℤ) else 0) : WithTop ℤ) +
      (↑(if rho2 = rho1 then (1 : ℤ) else 0) : WithTop ℤ) + 1) ≤ M := by
    exact le_trans (by exact_mod_cast hb1) hm1
  have hnot' : rho ≠ rho1 := Ne.symm hnot
  rcases eq_or_ne rho2 rho1 with h2 | h2
  · subst rho2
    norm_num [hnot, hnot'] at hbudget ⊢
    exact hbudget
  · have h2' : rho1 ≠ rho2 := Ne.symm h2
    simp [hnot, hnot', h2, h2'] at hbudget ⊢
    exact hbudget

private theorem soninTriple_count_le_of_budget_at_rho2
    {rho1 rho2 rho : ℂ} {l m2 : ℕ} {M : WithTop ℤ}
    (hnot : rho2 ≠ rho) (hnot1 : rho2 ≠ rho1)
    (hb2 : (if rho = rho2 then (l : ℤ) else 0) + 1 +
      (if rho1 = rho2 then 1 else 0) ≤ (m2 : ℤ))
    (hm2 : ((m2 : ℤ) : WithTop ℤ) ≤ M) :
    ((↑(if rho2 = rho1 then (1 : ℤ) else 0) : WithTop ℤ) +
      ((↑(if rho2 = rho2 then (1 : ℤ) else 0) : WithTop ℤ) +
        (↑(l : ℤ) : WithTop ℤ) * ↑(if rho2 = rho then (1 : ℤ) else 0))) ≤ M := by
  have hbudget : ((↑(if rho = rho2 then (l : ℤ) else 0) : WithTop ℤ) + 1 +
      (↑(if rho1 = rho2 then (1 : ℤ) else 0) : WithTop ℤ)) ≤ M := by
    exact le_trans (by exact_mod_cast hb2) hm2
  have hnot' : rho ≠ rho2 := Ne.symm hnot
  have hnot1' : rho1 ≠ rho2 := Ne.symm hnot1
  simp [hnot, hnot', hnot1, hnot1'] at hbudget ⊢
  exact hbudget

theorem analyticAt_soninTripleNF_of_threePointBudget
    {rho1 rho2 rho : ℂ} {l m1 m2 mr : ℕ}
    (hrho1re0 : 0 < rho1.re) (hrho1re1 : rho1.re < 1)
    (hrho2re0 : 0 < rho2.re) (hrho2re1 : rho2.re < 1)
    (hrhore0 : 0 < rho.re) (hrhore1 : rho.re < 1)
    (hm1 : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta rho1)
    (hm2 : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta rho2)
    (hmr : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta rho)
    (hb0 : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ (mr : ℤ))
    (hb1 : (if rho = rho1 then (l : ℤ) else 0) + (if rho2 = rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hb2 : (if rho = rho2 then (l : ℤ) else 0) + 1 + (if rho1 = rho2 then 1 else 0) ≤ (m2 : ℤ))
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    AnalyticAt ℂ (soninTripleNF rho1 rho2 rho l) z := by
  have hζAt : ∀ {w : ℂ}, 0 < w.re → w.re < 1 → AnalyticAt ℂ riemannZeta w := by
    intro w hw0 hw1
    apply analyticOn_riemannZeta w
    intro h
    rw [h] at hw1
    norm_num at hw1
  have hm1' : ((m1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt riemannZeta rho1 :=
    le_meromorphicOrderAt_of_le_analyticOrderAt (hζAt hrho1re0 hrho1re1) hm1
  have hm2' : ((m2 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt riemannZeta rho2 :=
    le_meromorphicOrderAt_of_le_analyticOrderAt (hζAt hrho2re0 hrho2re1) hm2
  have hmr' : ((mr : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt riemannZeta rho :=
    le_meromorphicOrderAt_of_le_analyticOrderAt (hζAt hrhore0 hrhore1) hmr
  apply analyticAt_soninTripleNF hz0 hz1
  by_cases hzrho : z = rho
  · subst z
    exact soninTriple_count_le_of_budget_at_rho hb0 hmr'
  by_cases hzrho1 : z = rho1
  · subst z
    exact soninTriple_count_le_of_budget_at_rho1 hzrho hb1 hm1'
  by_cases hzrho2 : z = rho2
  · subst z
    exact soninTriple_count_le_of_budget_at_rho2 hzrho hzrho1 hb2 hm2'
  simpa [hzrho, hzrho1, hzrho2] using
    (meromorphicOrderAt_nonneg_of_analyticAt (hζAt hz0 hz1))

/-- The functional equation supplies the left pure-tail datum from the reflected triple quotient.
This is the coefficient-faithful two-sided descent used by the two-omission Sonine system. -/
theorem exists_centralSonin_soninTriple_of_reflectedTail
    {rho1 rho2 rho : ℂ} {l : ℕ}
    (hana : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF rho1 rho2 rho l) z)
    {gRight : ℝ → ℂ} (hgRight : MemLp gRight 2 (volume.restrict (Ioi (1 : ℝ))))
    (hRight : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      soninTripleNF rho1 rho2 rho l s = headTailMellin 1 0 gRight s)
    (hanaMirror : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF (1 - rho1) (1 - rho2) (1 - rho) l) z)
    {gMirror : ℝ → ℂ} (hgMirror : MemLp gMirror 2 (volume.restrict (Ioi (1 : ℝ))))
    (hMirror : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      soninTripleNF (1 - rho1) (1 - rho2) (1 - rho) l s =
        headTailMellin 1 0 gMirror s) :
    ∃ v : SoninL2, v ∈ evenSubspace ∧ v ∈ centralSoninCarrier 1 ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0) ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s := by
  have hLeft : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      burnolChiFactor s * soninTripleNF rho1 rho2 rho l (1 - s) =
        headTailMellin 1 0 (fun t : ℝ => (-1 : ℂ) ^ l * gMirror t) s := by
    intro s hs1 hs2
    have hScale : headTailMellin 1 0 (fun t : ℝ => (-1 : ℂ) ^ l * gMirror t) s
        = (-1 : ℂ) ^ l * headTailMellin 1 0 gMirror s := by
      simp only [headTailMellin, zero_mul, zero_div, zero_add]
      calc
        (∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * ((-1 : ℂ) ^ l * gMirror t))
          = ∫ t in Ioi (1 : ℝ), (-1 : ℂ) ^ l * (((t : ℝ) : ℂ) ^ (-s) * gMirror t) := by
            refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
            ring
        _ = (-1 : ℂ) ^ l * ∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * gMirror t := by
            rw [MeasureTheory.integral_const_mul]
    rw [hScale, ← hMirror s hs1 hs2,
      soninTripleNF_reflect hana hanaMirror s hs1 hs2]
  exact exists_centralSonin_soninTriple_of_twoSidedTail hana hgRight hRight
    (hgMirror.const_mul ((-1 : ℂ) ^ l)) hLeft

/-- **Burnol's two-omission carrier.** Exact divisor multiplicity budgets on a triple quotient and
its reflected quotient produce one literal vector of `K₁`; both aperture constants vanish and its
completed Mellin transform is the prescribed triple quotient on the full critical strip. -/
theorem exists_centralSonin_soninTriple
    {rho1 rho2 rho : ℂ} {l m1 m2 mr : ℕ}
    (hrho10 : rho1 ≠ 0) (hrho11 : rho1 ≠ 1)
    (hrho20 : rho2 ≠ 0) (hrho21 : rho2 ≠ 1)
    (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) (hl : 1 ≤ l)
    (hm1 : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta rho1)
    (hm2 : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta rho2)
    (hmr : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta rho)
    (hb0 : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ (mr : ℤ))
    (hb1 : (if rho = rho1 then (l : ℤ) else 0) + (if rho2 = rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hb2 : (if rho = rho2 then (l : ℤ) else 0) + 1 + (if rho1 = rho2 then 1 else 0) ≤ (m2 : ℤ))
    (hana : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF rho1 rho2 rho l) z)
    (hm1R : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho1))
    (hm2R : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho2))
    (hmrR : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho))
    (hb0R : (l : ℤ) + (if 1 - rho2 = 1 - rho then 1 else 0)
      + (if 1 - rho1 = 1 - rho then 1 else 0) ≤ (mr : ℤ))
    (hb1R : (if 1 - rho = 1 - rho1 then (l : ℤ) else 0)
      + (if 1 - rho2 = 1 - rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hb2R : (if 1 - rho = 1 - rho2 then (l : ℤ) else 0) + 1
      + (if 1 - rho1 = 1 - rho2 then 1 else 0) ≤ (m2 : ℤ))
    (hanaMirror : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF (1 - rho1) (1 - rho2) (1 - rho) l) z) :
    ∃ v : SoninL2, v ∈ evenSubspace ∧ v ∈ centralSoninCarrier 1 ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0) ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s := by
  obtain ⟨gRight, hgRight, hRight⟩ := exists_tail_soninTripleNF
    hrho10 hrho11 hrho20 hrho21 hrho0 hrho1 hl hm1 hm2 hmr hb0 hb1 hb2
    (fun z hz1 hz2 => hana z (by linarith) hz2)
  have hrho1m0 : (1 : ℂ) - rho1 ≠ 0 := by
    intro h
    apply hrho11
    calc
      rho1 = 1 - (1 - rho1) := by ring
      _ = 1 - 0 := by rw [h]
      _ = 1 := by ring
  have hrho1m1 : (1 : ℂ) - rho1 ≠ 1 := by
    intro h
    apply hrho10
    calc
      rho1 = 1 - (1 - rho1) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  have hrho2m0 : (1 : ℂ) - rho2 ≠ 0 := by
    intro h
    apply hrho21
    calc
      rho2 = 1 - (1 - rho2) := by ring
      _ = 1 - 0 := by rw [h]
      _ = 1 := by ring
  have hrho2m1 : (1 : ℂ) - rho2 ≠ 1 := by
    intro h
    apply hrho20
    calc
      rho2 = 1 - (1 - rho2) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  have hrhom0 : (1 : ℂ) - rho ≠ 0 := by
    intro h
    apply hrho1
    calc
      rho = 1 - (1 - rho) := by ring
      _ = 1 - 0 := by rw [h]
      _ = 1 := by ring
  have hrhom1 : (1 : ℂ) - rho ≠ 1 := by
    intro h
    apply hrho0
    calc
      rho = 1 - (1 - rho) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  obtain ⟨gMirror, hgMirror, hMirror⟩ := exists_tail_soninTripleNF
    hrho1m0 hrho1m1 hrho2m0 hrho2m1 hrhom0 hrhom1 hl hm1R hm2R hmrR
    hb0R hb1R hb2R hanaMirror
  exact exists_centralSonin_soninTriple_of_reflectedTail hana hgRight hRight
    hanaMirror hgMirror hMirror

/-- The reflected multiplicity conditions in the two-omission carrier are consequences of the
original source budget.  No independent reflected divisor bookkeeping is needed. -/
theorem exists_centralSonin_soninTriple_of_symmetricBudget
    {rho1 rho2 rho : ℂ} {l m1 m2 mr : ℕ}
    (hrho1re0 : 0 < rho1.re) (hrho1re1 : rho1.re < 1)
    (hrho2re0 : 0 < rho2.re) (hrho2re1 : rho2.re < 1)
    (hrhore0 : 0 < rho.re) (hrhore1 : rho.re < 1) (hl : 1 ≤ l)
    (hm1 : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta rho1)
    (hm2 : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta rho2)
    (hmr : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta rho)
    (hb0 : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ (mr : ℤ))
    (hb1 : (if rho = rho1 then (l : ℤ) else 0) + (if rho2 = rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hb2 : (if rho = rho2 then (l : ℤ) else 0) + 1 + (if rho1 = rho2 then 1 else 0) ≤ (m2 : ℤ))
    (hana : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF rho1 rho2 rho l) z)
    (hanaMirror : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF (1 - rho1) (1 - rho2) (1 - rho) l) z) :
    ∃ v : SoninL2, v ∈ evenSubspace ∧ v ∈ centralSoninCarrier 1 ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0) ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s := by
  have hrho10 : rho1 ≠ 0 := by
    intro h
    rw [h] at hrho1re0
    norm_num at hrho1re0
  have hrho11 : rho1 ≠ 1 := by
    intro h
    rw [h] at hrho1re1
    norm_num at hrho1re1
  have hrho20 : rho2 ≠ 0 := by
    intro h
    rw [h] at hrho2re0
    norm_num at hrho2re0
  have hrho21 : rho2 ≠ 1 := by
    intro h
    rw [h] at hrho2re1
    norm_num at hrho2re1
  have hrho0 : rho ≠ 0 := by
    intro h
    rw [h] at hrhore0
    norm_num at hrhore0
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hrhore1
    norm_num at hrhore1
  have hm1R : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho1) := by
    rw [analyticOrderAt_riemannZeta_one_sub hrho1re0 hrho1re1]
    exact hm1
  have hm2R : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho2) := by
    rw [analyticOrderAt_riemannZeta_one_sub hrho2re0 hrho2re1]
    exact hm2
  have hmrR : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho) := by
    rw [analyticOrderAt_riemannZeta_one_sub hrhore0 hrhore1]
    exact hmr
  have hsub : ∀ u v : ℂ, ((1 : ℂ) - u = 1 - v) ↔ u = v := by
    intro u v
    constructor
    · intro h
      calc
        u = 1 - (1 - u) := by ring
        _ = 1 - (1 - v) := by rw [h]
        _ = v := by ring
    · intro h
      rw [h]
  have hb0R : (l : ℤ) + (if 1 - rho2 = 1 - rho then 1 else 0)
      + (if 1 - rho1 = 1 - rho then 1 else 0) ≤ (mr : ℤ) := by
    simpa only [hsub rho2 rho, hsub rho1 rho] using hb0
  have hb1R : (if 1 - rho = 1 - rho1 then (l : ℤ) else 0)
      + (if 1 - rho2 = 1 - rho1 then 1 else 0) + 1 ≤ (m1 : ℤ) := by
    simpa only [hsub rho rho1, hsub rho2 rho1] using hb1
  have hb2R : (if 1 - rho = 1 - rho2 then (l : ℤ) else 0) + 1
      + (if 1 - rho1 = 1 - rho2 then 1 else 0) ≤ (m2 : ℤ) := by
    simpa only [hsub rho rho2, hsub rho1 rho2] using hb2
  exact exists_centralSonin_soninTriple hrho10 hrho11 hrho20 hrho21 hrho0 hrho1 hl
    hm1 hm2 hmr hb0 hb1 hb2 hana hm1R hm2R hmrR hb0R hb1R hb2R hanaMirror

/-- The symmetric three-point budgets alone construct the two-omission `K₁` carrier.  The two
analyticity premises in the earlier assembly theorem are now discharged by
`analyticAt_soninTripleNF_of_threePointBudget` on the original and reflected triples. -/
theorem exists_centralSonin_soninTriple_of_sourceBudget
    {rho1 rho2 rho : ℂ} {l m1 m2 mr : ℕ}
    (hrho1re0 : 0 < rho1.re) (hrho1re1 : rho1.re < 1)
    (hrho2re0 : 0 < rho2.re) (hrho2re1 : rho2.re < 1)
    (hrhore0 : 0 < rho.re) (hrhore1 : rho.re < 1) (hl : 1 ≤ l)
    (hm1 : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta rho1)
    (hm2 : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta rho2)
    (hmr : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta rho)
    (hb0 : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ (mr : ℤ))
    (hb1 : (if rho = rho1 then (l : ℤ) else 0) + (if rho2 = rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hb2 : (if rho = rho2 then (l : ℤ) else 0) + 1 + (if rho1 = rho2 then 1 else 0) ≤ (m2 : ℤ)) :
    ∃ v : SoninL2, v ∈ evenSubspace ∧ v ∈ centralSoninCarrier 1 ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = 0) ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        extendedMellinContinuation 1 0 0 v s = soninTripleNF rho1 rho2 rho l s := by
  have hm1R : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho1) := by
    rw [analyticOrderAt_riemannZeta_one_sub hrho1re0 hrho1re1]
    exact hm1
  have hm2R : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho2) := by
    rw [analyticOrderAt_riemannZeta_one_sub hrho2re0 hrho2re1]
    exact hm2
  have hmrR : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta (1 - rho) := by
    rw [analyticOrderAt_riemannZeta_one_sub hrhore0 hrhore1]
    exact hmr
  have hsub : ∀ u v : ℂ, ((1 : ℂ) - u = 1 - v) ↔ u = v := by
    intro u v
    constructor
    · intro h
      calc
        u = 1 - (1 - u) := by ring
        _ = 1 - (1 - v) := by rw [h]
        _ = v := by ring
    · intro h
      rw [h]
  have hb0R : (l : ℤ) + (if 1 - rho2 = 1 - rho then 1 else 0)
      + (if 1 - rho1 = 1 - rho then 1 else 0) ≤ (mr : ℤ) := by
    simpa only [hsub rho2 rho, hsub rho1 rho] using hb0
  have hb1R : (if 1 - rho = 1 - rho1 then (l : ℤ) else 0)
      + (if 1 - rho2 = 1 - rho1 then 1 else 0) + 1 ≤ (m1 : ℤ) := by
    simpa only [hsub rho rho1, hsub rho2 rho1] using hb1
  have hb2R : (if 1 - rho = 1 - rho2 then (l : ℤ) else 0) + 1
      + (if 1 - rho1 = 1 - rho2 then 1 else 0) ≤ (m2 : ℤ) := by
    simpa only [hsub rho rho2, hsub rho1 rho2] using hb2
  have hrho1m0 : 0 < ((1 : ℂ) - rho1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hrho1m1 : ((1 : ℂ) - rho1).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hrho2m0 : 0 < ((1 : ℂ) - rho2).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hrho2m1 : ((1 : ℂ) - rho2).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hrhom0 : 0 < ((1 : ℂ) - rho).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hrhom1 : ((1 : ℂ) - rho).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact exists_centralSonin_soninTriple_of_symmetricBudget
    hrho1re0 hrho1re1 hrho2re0 hrho2re1 hrhore0 hrhore1 hl
    hm1 hm2 hmr hb0 hb1 hb2
    (fun z hz0 hz1 => analyticAt_soninTripleNF_of_threePointBudget
      hrho1re0 hrho1re1 hrho2re0 hrho2re1 hrhore0 hrhore1
      hm1 hm2 hmr hb0 hb1 hb2 hz0 hz1)
    (fun z hz0 hz1 => analyticAt_soninTripleNF_of_threePointBudget
      hrho1m0 hrho1m1 hrho2m0 hrho2m1 hrhom0 hrhom1
      hm1R hm2R hmrR hb0R hb1R hb2R (by linarith) hz1)

/-- **Burnol Proposition 6.5, finite-defect witness form.**  Once the triple quotient's selected
order is the retained jet `k`, symmetric divisor budgets produce a literal `K₁` witness which
annihilates precisely the shortened system: only the two named top jets are omitted. -/
theorem exists_twoPointOmittedEvaluatorWitness_of_symmetricBudget
    {rho1 rho2 rho : ℂ} {l m1 m2 mr k : ℕ}
    (hrho1re0 : 0 < rho1.re) (hrho1re1 : rho1.re < 1)
    (hrho2re0 : 0 < rho2.re) (hrho2re1 : rho2.re < 1)
    (hrhore0 : 0 < rho.re) (hrhore1 : rho.re < 1) (hl : 1 ≤ l)
    (hm1 : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta rho1)
    (hm2 : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta rho2)
    (hmr : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta rho)
    (hb0 : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ (mr : ℤ))
    (hb1 : (if rho = rho1 then (l : ℤ) else 0) + (if rho2 = rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hb2 : (if rho = rho2 then (l : ℤ) else 0) + 1 + (if rho1 = rho2 then 1 else 0) ≤ (m2 : ℤ))
    (hana : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF rho1 rho2 rho l) z)
    (hanaMirror : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
      AnalyticAt ℂ (soninTripleNF (1 - rho1) (1 - rho2) (1 - rho) l) z)
    (hk : meromorphicOrderAt riemannZeta rho
      - ((((if rho = rho1 then (1 : ℤ) else 0) + ((if rho = rho2 then (1 : ℤ) else 0)
        + (l : ℤ) * (if rho = rho then (1 : ℤ) else 0))) : ℤ) : WithTop ℤ)
        = ((k : ℤ) : WithTop ℤ)) :
    ∃ v : SoninL2, IsTwoPointOmittedEvaluatorWitness rho1 rho2 rho k v := by
  obtain ⟨v, hev, hK, hFour, hPhys, hMellin⟩ :=
    exists_centralSonin_soninTriple_of_symmetricBudget
      hrho1re0 hrho1re1 hrho2re0 hrho2re1 hrhore0 hrhore1 hl
      hm1 hm2 hmr hb0 hb1 hb2 hana hanaMirror
  refine ⟨v, isTwoPointOmittedEvaluatorWitness_of_exactMellin hev hK hFour hPhys hMellin ?_⟩
  rw [meromorphicOrderAt_extendedMellin_soninTriple_of_eq hMellin hrhore0 hrhore1]
  exact hk

/-- **Burnol Proposition 6.5, source-budget form.** The three literal divisor budgets, their
functional-equation reflection, and the exact retained order construct a `K₁` vector annihilating
the two-omission evaluator system. No separate analyticity hypothesis remains. -/
theorem exists_twoPointOmittedEvaluatorWitness_of_sourceBudget
    {rho1 rho2 rho : ℂ} {l m1 m2 mr k : ℕ}
    (hrho1re0 : 0 < rho1.re) (hrho1re1 : rho1.re < 1)
    (hrho2re0 : 0 < rho2.re) (hrho2re1 : rho2.re < 1)
    (hrhore0 : 0 < rho.re) (hrhore1 : rho.re < 1) (hl : 1 ≤ l)
    (hm1 : (m1 : ℕ∞) ≤ analyticOrderAt riemannZeta rho1)
    (hm2 : (m2 : ℕ∞) ≤ analyticOrderAt riemannZeta rho2)
    (hmr : (mr : ℕ∞) ≤ analyticOrderAt riemannZeta rho)
    (hb0 : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0) ≤ (mr : ℤ))
    (hb1 : (if rho = rho1 then (l : ℤ) else 0) + (if rho2 = rho1 then 1 else 0) + 1 ≤ (m1 : ℤ))
    (hb2 : (if rho = rho2 then (l : ℤ) else 0) + 1 + (if rho1 = rho2 then 1 else 0) ≤ (m2 : ℤ))
    (hk : meromorphicOrderAt riemannZeta rho
      - ((((if rho = rho1 then (1 : ℤ) else 0) + ((if rho = rho2 then (1 : ℤ) else 0)
        + (l : ℤ) * (if rho = rho then (1 : ℤ) else 0))) : ℤ) : WithTop ℤ)
        = ((k : ℤ) : WithTop ℤ)) :
    ∃ v : SoninL2, IsTwoPointOmittedEvaluatorWitness rho1 rho2 rho k v := by
  obtain ⟨v, hev, hK, hFour, hPhys, hMellin⟩ :=
    exists_centralSonin_soninTriple_of_sourceBudget
      hrho1re0 hrho1re1 hrho2re0 hrho2re1 hrhore0 hrhore1 hl
      hm1 hm2 hmr hb0 hb1 hb2
  refine ⟨v, isTwoPointOmittedEvaluatorWitness_of_exactMellin hev hK hFour hPhys hMellin ?_⟩
  rw [meromorphicOrderAt_extendedMellin_soninTriple_of_eq hMellin hrhore0 hrhore1]
  exact hk

/-- **Burnol Proposition 6.5, retained-jet form.** A literal retained jet and literal validity of
the two omitted top jets determine the required triple-quotient exponent. Hence they construct a
coefficient-faithful `K₁` finite-defect witness without a separately postulated selected-order
equality. The formula includes all collisions among the selected point and the two omissions. -/
theorem exists_twoPointOmittedEvaluatorWitness_of_retainedJet
    {rho1 rho2 rho : ℂ} {k : ℕ}
    (hrho1re0 : 0 < rho1.re) (hrho1re1 : rho1.re < 1)
    (hrho2re0 : 0 < rho2.re) (hrho2re1 : rho2.re < 1)
    (hrhore0 : 0 < rho.re) (hrhore1 : rho.re < 1)
    (homit1 : twoPointOmissionMultiplicity rho1 rho2 rho1 ≤ zetaStripMultiplicity rho1)
    (homit2 : twoPointOmissionMultiplicity rho1 rho2 rho2 ≤ zetaStripMultiplicity rho2)
    (hk : k < zetaStripMultiplicity rho - twoPointOmissionMultiplicity rho1 rho2 rho) :
    ∃ v : SoninL2, IsTwoPointOmittedEvaluatorWitness rho1 rho2 rho k v := by
  let m : ℂ → ℕ := zetaStripMultiplicity
  let l : ℕ := m rho - twoPointOmissionMultiplicity rho1 rho2 rho - k
  have hl : 1 ≤ l := by
    dsimp [l, m]
    omega
  have hfin1 : analyticOrderAt riemannZeta rho1 ≠ ⊤ :=
    analyticOrderAt_riemannZeta_ne_top_of_strip hrho1re0 hrho1re1
  have hfin2 : analyticOrderAt riemannZeta rho2 ≠ ⊤ :=
    analyticOrderAt_riemannZeta_ne_top_of_strip hrho2re0 hrho2re1
  have hfin : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    analyticOrderAt_riemannZeta_ne_top_of_strip hrhore0 hrhore1
  have hm1 : (m rho1 : ℕ∞) ≤ analyticOrderAt riemannZeta rho1 := by
    dsimp [m, zetaStripMultiplicity]
    exact le_of_eq (ENat.coe_toNat hfin1)
  have hm2 : (m rho2 : ℕ∞) ≤ analyticOrderAt riemannZeta rho2 := by
    dsimp [m, zetaStripMultiplicity]
    exact le_of_eq (ENat.coe_toNat hfin2)
  have hmr : (m rho : ℕ∞) ≤ analyticOrderAt riemannZeta rho := by
    dsimp [m, zetaStripMultiplicity]
    exact le_of_eq (ENat.coe_toNat hfin)
  obtain ⟨hb0, hb1, hb2⟩ := twoPoint_literal_triple_budgets_of_retained_jet
    (m := m) (k := k) (by simpa [m] using hk)
    (by simpa [m] using homit1) (by simpa [m] using homit2)
  have hb0' : (l : ℤ) + (if rho2 = rho then 1 else 0) + (if rho1 = rho then 1 else 0)
      ≤ (m rho : ℤ) := by
    dsimp [l]
    exact_mod_cast hb0
  have hb1' : (if rho = rho1 then (l : ℤ) else 0) + (if rho2 = rho1 then 1 else 0) + 1
      ≤ (m rho1 : ℤ) := by
    dsimp [l]
    exact_mod_cast hb1
  have hb2' : (if rho = rho2 then (l : ℤ) else 0) + 1 + (if rho1 = rho2 then 1 else 0)
      ≤ (m rho2 : ℤ) := by
    dsimp [l]
    exact_mod_cast hb2
  have hζ : meromorphicOrderAt riemannZeta rho = ((m rho : ℤ) : WithTop ℤ) := by
    dsimp [m, zetaStripMultiplicity]
    exact meromorphicOrderAt_riemannZeta_eq_toNat_of_strip hrhore0 hrhore1
  have htarget : meromorphicOrderAt riemannZeta rho
      - (((↑(if rho = rho1 then (1 : ℤ) else 0) : WithTop ℤ) +
        ((↑(if rho = rho2 then (1 : ℤ) else 0) : WithTop ℤ) +
          (↑(l : ℤ) : WithTop ℤ) * ↑(if rho = rho then (1 : ℤ) else 0))))
        = ((k : ℤ) : WithTop ℤ) := by
    rw [hζ, twoPoint_triple_divisor_count_eq_omission_add]
    simpa [m, l] using twoPoint_retained_order_sub_omission_eq
      (m := zetaStripMultiplicity rho)
      (d := twoPointOmissionMultiplicity rho1 rho2 rho) (k := k) hk
  exact exists_twoPointOmittedEvaluatorWitness_of_sourceBudget
    hrho1re0 hrho1re1 hrho2re0 hrho2re1 hrhore0 hrhore1 hl
    hm1 hm2 hmr hb0' hb1' hb2' htarget

end

end RHTower
