import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FiniteTopLayersNeedNoSeparation
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeWindowTransfer
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration

/-!
# Length-dependent floors give the asymptotic abscissa law

A finite nonempty exceptional layer has a maximal real part and finitely many active
positive ordinates. Half-period deletion detects it on a window whose length depends only
on their number. Thus floors on arbitrarily late windows of each length `(k+1)π/67`
imply the asymptotic abscissa law, even when the floor depends on the length.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- An active zeta exponent is the translate by one half of an actual zero. -/
theorem mem_zeta_of_active_exponent {z : ℂ}
    (hz : evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0) :
    (1 / 2 : ℂ) + z ∈ zetaZeroConfig.carrier := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · exact h
  · have hhalf : conj (1 / 2 : ℂ) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    simpa only [map_add, hhalf, Complex.conj_conj] using
      _root_.RHTower.conj_mem_zetaZeroConfig h

/-- Failure of AAL supplies a finite nonempty active top spectrum with positive depth. -/
theorem exists_finite_top_of_not_abscissaLaw
    (hnot : ¬ _root_.RHTower.AsymptoticAbscissaLaw) :
    ∃ b : ℝ, 0 < b ∧ TopDepth zetaZeroConfig b ∧ ∃ S : Finset ℂ,
      (∀ z, z ∈ S ↔ z ∈ positiveTopSupport zetaZeroConfig b) ∧ S.Nonempty := by
  classical
  have hnot' : ¬ AbscissaLaw zetaZeroConfig :=
    fun h => hnot (ZetaAbscissa.zetaZeroConfig_abscissaLaw_iff.mp h)
  unfold AbscissaLaw AbscissaLawAt at hnot'
  push Not at hnot'
  obtain ⟨h, hh, hfin, ρ, hρ, hgt⟩ := hnot'
  obtain ⟨ρ₀, hρ₀, hmax⟩ := hfin.exists_maximalFor Complex.re
    (rightOf zetaZeroConfig h) ⟨ρ, hρ, hgt⟩
  have hre : 1 / 2 + h < ρ₀.re := hρ₀.2
  have hall : ∀ τ ∈ zetaZeroConfig.carrier, τ.re ≤ ρ₀.re := by
    intro τ hτ
    by_cases ht : 1 / 2 + h < τ.re
    · by_contra hn
      exact (not_le.mpr (lt_of_not_ge hn)) (hmax ⟨hτ, ht⟩ (lt_of_not_ge hn).le)
    · linarith only [hre, le_of_not_gt ht]
  let b := ρ₀.re - 1 / 2
  have hb : 0 < b := by dsimp [b]; linarith only [hre, hh]
  have htop : TopDepth zetaZeroConfig b := by
    intro z hz
    have hbound := hall _ (mem_zeta_of_active_exponent hz)
    have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
    rw [he] at hbound
    dsimp [b]
    linarith only [hbound]
  have hfinite : (positiveTopSupport zetaZeroConfig b).Finite := by
    apply (hfin.preimage (f := fun z : ℂ => (1 / 2 : ℂ) + z)
      (add_right_injective (1 / 2 : ℂ)).injOn).subset
    intro z hz
    refine ⟨mem_zeta_of_active_exponent hz.2.2, ?_⟩
    have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
    rw [he, hz.1]
    dsimp [b]
    linarith only [hre]
  have hnonempty : (positiveTopSupport zetaZeroConfig b).Nonempty := by
    have he := evenCoeff_spline_sees hρ₀.1 (by linarith only [hre, hh])
    have hzre : (ρ₀ - 1 / 2).re = b := by simp [b]
    rcases lt_or_gt_of_ne (evenCoeff_spline_real he) with hn | hp
    · refine ⟨conj (ρ₀ - 1 / 2), ?_⟩
      refine ⟨by simpa only [Complex.conj_re] using hzre,
        by simpa only [Complex.conj_im] using neg_pos.mpr hn, ?_⟩
      rw [evenCoeff_conj]
      intro hzero
      exact he (by simpa only [Complex.conj_conj, map_zero] using congrArg conj hzero)
    · exact ⟨ρ₀ - 1 / 2, hzre, hp, he⟩
  exact ⟨b, hb, htop, hfinite.toFinset, fun z => Set.Finite.mem_toFinset hfinite,
    hfinite.toFinset_nonempty.mpr hnonempty⟩

/-- Floors may depend on window length. Their existence on arbitrarily late windows of
each length `(k+1)π/67` already gives AAL. -/
theorem asymptoticAbscissaLaw_of_lengthDependent_floors
    (hfloor : ∀ k : ℕ, ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ u ∈ Icc T (T + ((k : ℝ) + 1) * Real.pi / 67),
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  obtain ⟨K, hK⟩ := hfloor S.card
  obtain ⟨U, hU⟩ := zeta_finite_top_breaks_every_floor hb htop S hS hne le_rfl K
  obtain ⟨T, hT, hfloorT⟩ := hK U
  obtain ⟨u, hu, hneg⟩ := hU T hT
  exact (not_lt.mpr (hfloorT u hu)) hneg

/-- A floor of any exponent below a finite top depth fails on every sufficiently late
window of length `(k+1)π/67`. -/
theorem zeta_finite_top_breaks_exponential_floor {b α : ℝ} (hb : 0 < b) (hαb : α < b)
    (htop : TopDepth zetaZeroConfig b) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport zetaZeroConfig b)
    (hne : S.Nonempty) {k : ℕ} (hk : S.card ≤ k) (M : ℝ) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T →
      ∃ u ∈ Icc T (T + ((k : ℝ) + 1) * Real.pi / 67),
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re <
          -(M * Real.exp (α * u)) := by
  obtain ⟨ε, V, hε, hwin⟩ := zeta_finite_top_negative_windows hb htop S hS hne hk
  have hlim : Tendsto (fun u : ℝ => |M| * Real.exp ((α - b) * u)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hαb))).const_mul |M|
  obtain ⟨W, hW⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max V W, fun T hT => ?_⟩
  obtain ⟨u, hu, hneg⟩ := hwin T ((le_max_left _ _).trans hT)
  have hsmall := hW u (((le_max_right _ _).trans hT).trans hu.1)
  refine ⟨u, hu, ?_⟩
  by_contra hn
  have hbound := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (Real.exp_pos (-(b * u))).le
  have he : -(M * Real.exp (α * u)) * Real.exp (-(b * u)) =
      -(M * Real.exp ((α - b) * u)) := by
    rw [neg_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he] at hbound
  have hm := mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos ((α - b) * u)).le
  change normTrace zetaZeroConfig b u < -ε at hneg
  change -(M * Real.exp ((α - b) * u)) ≤ normTrace zetaZeroConfig b u at hbound
  linarith only [hneg, hsmall, hm, hbound]

/-- The same length-dependent floors at prime logarithms give AAL. Prime gaps cost an
exponent strictly smaller than the depth of any nonempty finite top layer. -/
theorem asymptoticAbscissaLaw_of_lengthDependent_prime_floors
    (hfloor : ∀ k : ℕ, ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → Real.log p ∈ Icc T (T + ((k : ℝ) + 1) * Real.pi / 67) →
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  let L : ℝ := ((S.card : ℝ) + 1) * Real.pi / 67
  obtain ⟨k, hk⟩ := exists_nat_gt (max 2 L * 134 / Real.pi)
  let R : ℝ := ((k : ℝ) + 1) * Real.pi / 134
  have hRlarge : max 2 L ≤ R := by
    have hmul := (div_lt_iff₀ Real.pi_pos).mp hk
    dsimp [R]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 134)).mpr
    nlinarith only [hmul, Real.pi_pos]
  have hRtwo : 2 ≤ R := (le_max_left _ _).trans hRlarge
  have hLR : L ≤ R := (le_max_right _ _).trans hRlarge
  have hlength : ((k : ℝ) + 1) * Real.pi / 67 = 2 * R := by dsimp [R]; ring
  obtain ⟨K, hK⟩ := hfloor k
  have hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ R →
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
    intro U
    obtain ⟨T, hT, hf⟩ := hK (U - R)
    refine ⟨T + R, by linarith only [hT], fun p hp hlog => hf p hp ?_⟩
    rw [hlength]
    obtain ⟨hlo, hhi⟩ := abs_le.mp hlog
    constructor <;> linarith only [hlo, hhi]
  let α := max 0 (b - 1 / 3)
  have hα : 0 ≤ α := le_max_left _ _
  have hαb : α < b := max_lt hb (by linarith)
  have hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b := by
    intro ρ hρ
    by_cases hre : 1 / 2 < ρ.re
    · have hx := htop (ρ - 1 / 2) (evenCoeff_spline_sees hρ hre)
      have he : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
      rw [he] at hx
      linarith only [hx]
    · linarith only [le_of_not_gt hre, hb]
  have hshape : ∀ᶠ T : ℝ in atTop, 2 ≤ R ∧ R ≤ T :=
    (eventually_ge_atTop R).mono fun _ ht => ⟨hRtwo, ht⟩
  obtain ⟨M, hM⟩ := prime_windows_transfer temperedConfig_zetaZeroConfig hb.le hα
    (le_max_right _ _) (fun _ => R) hshape hwidth hprime
  obtain ⟨U, hU⟩ := zeta_finite_top_breaks_exponential_floor hb hαb htop S hS hne le_rfl M
  obtain ⟨T, hT, hf⟩ := hM (U + R / 2)
  obtain ⟨u, hu, hneg⟩ := hU (T - R / 2) (by linarith only [hT])
  have hu' : |u - T| ≤ R / 2 := by
    change T - R / 2 ≤ u ∧ u ≤ T - R / 2 + L at hu
    rw [abs_le]
    constructor <;> linarith only [hu.1, hu.2, hLR]
  exact (not_lt.mpr (hf u hu')) hneg

#print axioms asymptoticAbscissaLaw_of_lengthDependent_floors
#print axioms asymptoticAbscissaLaw_of_lengthDependent_prime_floors

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
