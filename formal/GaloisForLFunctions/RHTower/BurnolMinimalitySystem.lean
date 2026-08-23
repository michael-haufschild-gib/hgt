import GaloisForLFunctions.RHTower.BurnolMinimalWitness

/-!
# Minimality of the evaluator system at the critical aperture

Burnol's Theorem 6.3, minimality half.  For every nontrivial zero `ρ` and every jet index
`k < m_ρ` there is a *nonzero* vector of `L₁` whose continued Mellin transform vanishes to the full
order `m_{ρ'}` at every other nontrivial zero `ρ'`, and to order exactly `k` at `ρ`.  In the jet
language in which completeness is stated (`eq_zero_of_zeta_dvd_extendedMellin_one_le`), this says
precisely that the evaluator `Y¹_{ρ,k}` is not in the closed span of the others: the witness is
orthogonal to all of them and not to it.

The witness is Burnol's dual vector, the inverse Mellin transform of `ζ(s)/(s-ρ)^{m_ρ-k}`.

## Main results

* `meromorphicOrderAt_zetaDivPow_of_ne`, `meromorphicOrderAt_zetaDivPow_self`
* `exists_minimality_witness` — **Theorem 6.3, minimality half.**
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem meromorphicOrderAt_zetaDivPow_of_ne {ρ : ℂ} (l : ℕ) {z : ℂ} (hz1 : z ≠ 1) (hzρ : z ≠ ρ) :
    meromorphicOrderAt (zetaDivPow ρ l) z = meromorphicOrderAt riemannZeta z := by
  have hfun : zetaDivPow ρ l = riemannZeta / fun w : ℂ => (w - ρ) ^ l := by
    funext w
    rw [zetaDivPow, Pi.div_apply]
  have hζ : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z (by simpa using hz1)
  rw [hfun, meromorphicOrderAt_div hζ.meromorphicAt (analyticAt_sub_const_pow ρ l z).meromorphicAt,
    meromorphicOrderAt_sub_pow_of_ne l hzρ, sub_zero]

theorem meromorphicOrderAt_zetaDivPow_self {ρ : ℂ} (l : ℕ) (hρ1 : ρ ≠ 1) :
    meromorphicOrderAt (zetaDivPow ρ l) ρ
      = meromorphicOrderAt riemannZeta ρ - ((l : ℤ) : WithTop ℤ) := by
  have hfun : zetaDivPow ρ l = riemannZeta / fun w : ℂ => (w - ρ) ^ l := by
    funext w
    rw [zetaDivPow, Pi.div_apply]
  have hζ : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  rw [hfun, meromorphicOrderAt_div hζ.meromorphicAt (analyticAt_sub_const_pow ρ l ρ).meromorphicAt,
    meromorphicOrderAt_sub_pow]

theorem analyticOrderAt_riemannZeta_ne_top_of_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
  exact xi_orderAt_ne_top ρ

/-- **Theorem 6.3, minimality half.**  For every nontrivial zero `ρ` and every jet index `k` below
its multiplicity, `L₁` contains a vector whose continued Mellin transform is divisible by `ζ` at
every other nontrivial zero but has order exactly `k` at `ρ`. -/
theorem exists_minimality_witness {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {k : ℕ}
    (hk : (k : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    ∃ (v : SoninL2) (c d : ℂ), v ∈ evenSubspace ∧ v ∈ centralSoninExtendedCarrier 1 ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = d) ∧
      (∀ ρ' : ℂ, 0 < ρ'.re → ρ'.re < 1 → ρ' ≠ ρ →
        meromorphicOrderAt riemannZeta ρ'
          ≤ meromorphicOrderAt (extendedMellinContinuation 1 c d v) ρ') ∧
      meromorphicOrderAt (extendedMellinContinuation 1 c d v) ρ = ((k : ℤ) : WithTop ℤ) := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top_of_strip h0 h1
  set m : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hm
  have hmeq : ((m : ℕ) : ℕ∞) = analyticOrderAt riemannZeta ρ := ENat.coe_toNat hfin
  have hkm : k < m := by
    rw [← hmeq] at hk
    exact_mod_cast hk
  set l : ℕ := m - k with hldef
  have hl : 1 ≤ l := by omega
  have hlm : l ≤ m := by omega
  have hord : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ρ := by
    rw [← hmeq]
    exact_mod_cast hlm
  obtain ⟨v, c, d, hev, hmem, hc, hd, hMeq⟩ := exists_extendedSonin_zetaDivPow h0 h1 hl hord
  refine ⟨v, c, d, hev, hmem, hc, hd, ?_, ?_⟩
  · intro ρ' hρ'0 hρ'1 hρ'ne
    have hρ'1' : ρ' ≠ 1 := by
      intro h; rw [h] at hρ'1; simp at hρ'1
    have hloc : extendedMellinContinuation 1 c d v =ᶠ[𝓝 ρ'] zetaDivPowNF ρ l := by
      filter_upwards [isOpen_openStrip.mem_nhds (⟨hρ'0, hρ'1⟩ : ρ' ∈ {z : ℂ | 0 < z.re ∧ z.re < 1})]
        with z hz
      exact hMeq z hz.1 hz.2
    rw [meromorphicOrderAt_congr (hloc.filter_mono nhdsWithin_le_nhds),
      meromorphicOrderAt_zetaDivPowNF ρ l ρ',
      meromorphicOrderAt_zetaDivPow_of_ne l hρ'1' hρ'ne]
  · have hloc : extendedMellinContinuation 1 c d v =ᶠ[𝓝 ρ] zetaDivPowNF ρ l := by
      filter_upwards [isOpen_openStrip.mem_nhds (⟨h0, h1⟩ : ρ ∈ {z : ℂ | 0 < z.re ∧ z.re < 1})]
        with z hz
      exact hMeq z hz.1 hz.2
    rw [meromorphicOrderAt_congr (hloc.filter_mono nhdsWithin_le_nhds),
      meromorphicOrderAt_zetaDivPowNF ρ l ρ,
      meromorphicOrderAt_zetaDivPow_self l hρ1]
    have hζ : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
    have hzord : meromorphicOrderAt riemannZeta ρ = ((m : ℤ) : WithTop ℤ) := by
      rw [hζ.meromorphicOrderAt_eq, ← hmeq]
      simp
    rw [hzord]
    have : ((m : ℤ) : WithTop ℤ) - ((l : ℤ) : WithTop ℤ) = (((m : ℤ) - (l : ℤ)) : ℤ) := by
      norm_cast
    rw [this]
    congr 1
    omega

end

end RHTower
