import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePacketsOnTheDegreePointsCarryWeilsArchimedeanForm
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion
import GaloisForLFunctions.RHTower.WeilPoleWeightBelowOneEmpty
import GaloisForLFunctions.RHTower.WeilLevyQuarterWindowHarmonicDoubling

/-!
# The pairing of the degree points is the pole minus Weil's functional

In the unitary normalization the intersection number of `Γ_m` and `Γ_{mk}` is
`Γ_m·Γ_{mk}/√(m·mk) = Λ(k)/√k + ω(log k)`: the contact of the two graphs in the arithmetic square
plus the Lévy density of the jets (`frobeniusIntersection_div_sqrt`). On a packet sampled on the
degree points the two parts enter with different masses. The jets are a density on pairs of
points and carry the masses `1/m` and `1/n` of both. A contact is a point of `Γ_m ∩ Γ_n` and
carries one mass, that of the lower degree point.

* **The contacts on a packet** (`tendsto_degreeContact`): for every `k`,
  `Σ_m f_m f_{mk}/m → h(log k)`, `h` the autocorrelation of `f`, because `log(mk/N)` is
  `log(m/N) + log k` exactly. So the contacts, each with the mass of its lower point, tend to
  `Σ_{k ≥ 2} (Λ(k)/√k)·h(log k)`.
* **The prime part of Weil's functional** (`re_weilFullFunctional_packet`): for a real packet,
  Weil's functional is its pole and archimedean part minus `2 Σ_{k ≥ 2} (Λ(k)/√k)·h(log k)`.
* **The whole pairing** (`tendsto_degreeForm_add_contacts`): the jets with both masses, plus the
  contacts with one mass, minus the masses times `log(n/2π)`, tend to the pole term minus Weil's
  functional of the packet.
* **The sign** (`riemannHypothesis_iff_degreePairing_le_pole`,
  `riemannHypothesis_iff_degreePairing_le_degrees`): the Riemann hypothesis holds iff for every
  packet the limit of the pairing of the degree points is at most the pole term, which is
  `2 (∫ f e^{−u/2})(∫ f e^{u/2})`, twice the product of the two degrees of the packet. This is the
  inequality of Castelnuovo and Severi for the divisor `Σ f_n μ_n Γ_n` on the degree points.

* **The sign on short packets** (`weilFullFunctional_packet_nonneg_of_short`,
  `tendsto_degreePairing_le_pole_of_short`): a packet of width below `log 2` meets no contact,
  because its autocorrelation vanishes at the logarithms of the integers `k ≥ 2`. For a
  nonnegative packet of width at most `12/25` the inequality holds without hypothesis, by the
  positivity of the archimedean form on such windows.

So Weil's form is the finite part of the pairing of the degree points, with prime part the
contact orders of the arithmetic square, archimedean part the jets and the one counterterm
`log(n/2π)`. Its sign is known where no contact enters; where the contacts enter it is the
Riemann hypothesis.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.SurfaceOfSpecZ

local notation "ω" => _root_.RHTower.archLevyDensity

/-! ### The unitary intersection number of two graphs in divisibility -/

/-- The contact of `Γ_m` and `Γ_{mk}` in the unitary normalization: `Λ(k)/√k`. -/
def contactWeight (k : ℕ) : ℝ := Λ k / Real.sqrt k

/-- **The unitary intersection number of `Γ_m` and `Γ_{mk}`** is the contact weight plus the Lévy
density of the jets at the displacement `log k`. -/
theorem frobeniusIntersection_div_sqrt {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) :
    frobeniusIntersection m (m * k) / Real.sqrt ((m : ℝ) * ((m * k : ℕ) : ℝ)) =
      contactWeight k + ω (Real.log k) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hsq : Real.sqrt ((m : ℝ) * ((m * k : ℕ) : ℝ)) = m * Real.sqrt k := by
    rw [Nat.cast_mul, ← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hm'.le]
  have hk2 : (k : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hinv : (1 : ℝ) - ((k : ℝ)⁻¹) ^ 2 ≠ 0 := by
    have : ((k : ℝ)⁻¹) ^ 2 < 1 := by
      rw [inv_pow, inv_lt_one_iff₀]
      right
      nlinarith
    linarith
  rw [frobeniusIntersection_mul_eq_mul_pointCount hm hk, pointCount_eq hk, hsq, contactWeight,
    archLevyDensity_log hk0, Real.sqrt_inv]
  field_simp
  ring

/-! ### The autocorrelation of a real packet as a Weil test -/

theorem weilTest_packet (f : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) x =
      ((packetAutocorr f x : ℝ) : ℂ) := by
  have h := integral_ofReal (𝕜 := ℂ) (μ := volume) (f := fun u => f u * f (u + -x))
  rw [_root_.RHTower.WeilSpectral.weilTest_apply, ← packetAutocorr_neg, packetAutocorr]
  refine (integral_congr_ae (Eventually.of_forall fun u => ?_)).trans h
  simp [sub_eq_add_neg]

theorem weilTest_packet_translate (f : ℝ → ℝ) (s : ℝ) :
    EF.weilTest (fun u => ((f (u - s) : ℝ) : ℂ)) (fun u => ((f (u - s) : ℝ) : ℂ)) =
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) := by
  funext x
  rw [weilTest_packet (fun u => f (u - s)) x, weilTest_packet f x, packetAutocorr_translate]

/-- **The prime part of Weil's functional of a real packet**: twice the contact weights against
the autocorrelation at the logarithms. -/
theorem re_weilFullFunctional_packet (f : ℝ → ℝ) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) :
    (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      _root_.RHTower.WeilOneSided.weilArchRe
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
        2 * ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr f (Real.log k) := by
  have hterm : ∀ n : ℕ,
      (((if 2 ≤ n then (Λ n : ℝ) / Real.sqrt n else 0 : ℝ)) : ℂ) *
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (Real.log n) +
            EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-Real.log n)) =
        (((if n ∈ Icc 2 Q then 2 * (contactWeight n * packetAutocorr f (Real.log n)) else 0 :
          ℝ)) : ℂ) := by
    intro n
    rw [weilTest_packet, weilTest_packet, packetAutocorr_neg]
    by_cases h2 : 2 ≤ n
    · by_cases hQn : n ≤ Q
      · rw [if_pos h2, if_pos (Finset.mem_Icc.mpr ⟨h2, hQn⟩), contactWeight]
        push_cast
        ring
      · rw [if_pos h2, if_neg (fun h => hQn (Finset.mem_Icc.mp h).2), hQ n (not_le.mp hQn)]
        simp
    · rw [if_neg h2, if_neg (fun h => h2 (Finset.mem_Icc.mp h).1)]
      simp
  have hT : ∑' n : ℕ, (((if 2 ≤ n then (Λ n : ℝ) / Real.sqrt n else 0 : ℝ)) : ℂ) *
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (Real.log n) +
          EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-Real.log n)) =
      ((2 * ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr f (Real.log k) : ℝ) : ℂ) := by
    rw [tsum_congr hterm, tsum_eq_sum (s := Icc 2 Q) (fun n hn => by rw [if_neg hn]; simp),
      Finset.sum_congr rfl (fun n hn => by rw [if_pos hn]), Finset.mul_sum]
    push_cast
    rfl
  unfold _root_.RHTower.weilFullFunctional _root_.RHTower.WeilOneSided.weilArchRe
  rw [hT]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  ring

/-! ### The contacts on a packet -/

/-- The contacts of the degree points on a packet: the contact of `Γ_m` and `Γ_{mk}` with the mass
`1/m` of its lower point. -/
def degreeContact (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 L, contactWeight k *
    ∑ m ∈ Ioc N (N + L * N), degreeSample f N m * degreeSample f N (m * k) / m

/-- The pairs `(m, mk)` on a packet: a Riemann sum of `f(u)f(u + log k)`. -/
theorem tendsto_contactRow {f : ℝ → ℝ} (hcont : Continuous f) {L : ℕ} (hL : 1 ≤ L) {k : ℕ}
    (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ∑ m ∈ Ioc N (N + L * N),
        degreeSample f N m * degreeSample f N (m * k) / m) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + L), f u * f (u + Real.log k))) := by
  have hG : Continuous fun u => f u * f (u + Real.log k) :=
    hcont.mul (hcont.comp (continuous_id.add continuous_const))
  refine (tendsto_degreeSum hG hL).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log (((m * k : ℕ) : ℝ) / N) = Real.log ((m : ℝ) / N) + Real.log k := by
    rw [Nat.cast_mul, mul_div_right_comm, Real.log_mul (by positivity) hk'.ne']
  show f (Real.log ((m : ℝ) / N)) * f (Real.log ((m : ℝ) / N) + Real.log k) / m =
    degreeSample f N m * degreeSample f N (m * k) / m
  rw [degreeSample, degreeSample, hlog]

theorem tendsto_degreeContact {f : ℝ → ℝ} (hcont : Continuous f) {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (degreeContact f L) atTop
      (𝓝 (∑ k ∈ Icc 2 L, contactWeight k *
        ∫ u in (0 : ℝ)..Real.log (1 + L), f u * f (u + Real.log k))) :=
  tendsto_finsetSum _ fun k hk =>
    (tendsto_contactRow hcont hL (by
      have := (Finset.mem_Icc.mp hk).1
      omega)).const_mul _

/-! ### The whole pairing -/

/-- The window of a packet supported in `[log 3, log K]`. -/
theorem window_of_support {f : ℝ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    ∀ u, u ≤ Real.log 3 ∨ Real.log (1 + ((3 * K : ℕ) : ℝ)) - Real.log 3 ≤ u → f u = 0 := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h3K : ((3 * K : ℕ) : ℝ) = 3 * K := by
    push_cast
    ring
  have hcK : Real.log K ≤ Real.log (1 + ((3 * K : ℕ) : ℝ)) - Real.log 3 := by
    rw [h3K, ← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by
      rw [le_div_iff₀ (by norm_num)]
      linarith)
  exact fun u hu => hsupp u (hu.imp id fun h => hcK.trans h)

/-- **The pairing of the degree points on a packet is the pole minus Weil's functional.** The
jets with the masses of both points, plus the contacts with the mass of the lower point, minus the
masses times `log(n/2π)`, tend to the pole term minus Weil's functional of the packet. -/
theorem tendsto_degreeForm_add_contacts {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N) atTop
      (𝓝 ((_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re -
          (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re)) := by
  have hcont := hf.continuous
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hL3 : 1 ≤ 3 * K := by omega
  have hsuppW := window_of_support hK hsupp
  have h1L : (0 : ℝ) < 1 + ((3 * K : ℕ) : ℝ) := by positivity
  have hQ : ∀ n : ℕ, 3 * K < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_window hδ hsuppW (Real.log_le_log h1L (by
      have : ((3 * K : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith))
  have h1 := tendsto_degreeForm hf hfc hK hsupp
  have h2 := (tendsto_degreeContact hcont hL3).const_mul 2
  have hsum : ∑ k ∈ Icc 2 (3 * K), contactWeight k *
        ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u * f (u + Real.log k) =
      ∑ k ∈ Icc 2 (3 * K), contactWeight k * packetAutocorr f (Real.log k) :=
    Finset.sum_congr rfl fun k _ => by
      rw [packetAutocorr_eq_integral_window hδ hsuppW]
  have hfull := re_weilFullFunctional_packet f hQ
  have hlim := h1.add h2
  rw [hsum] at hlim
  have e : (_root_.RHTower.weilPoleTerm
          (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re -
        (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
          (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re =
      -(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re) +
        2 * ∑ k ∈ Icc 2 (3 * K), contactWeight k * packetAutocorr f (Real.log k) := by
    have hfull' : (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
          (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re =
        _root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          2 * ∑ k ∈ Icc 2 (3 * K), contactWeight k * packetAutocorr f (Real.log k) := hfull
    rw [hfull']
    ring
  rw [e]
  exact hlim

/-! ### The sign -/

/-- Every packet has a translate supported in a window above the scale. -/
theorem exists_translate_window {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    ∃ (s : ℝ) (K : ℕ), 1 ≤ K ∧ ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g (u - s) = 0 := by
  obtain ⟨A, hA⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ u, g u ≠ 0 → |u| ≤ A := fun u hu => by
    have := hA (subset_tsupport _ hu)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  obtain ⟨B, hB0, hAB⟩ : ∃ B : ℝ, 0 < B ∧ A < B := ⟨max A 0 + 1, by positivity, by
    have := le_max_left A 0
    linarith⟩
  have hexp : 0 < Real.exp (2 * B + Real.log 3) := Real.exp_pos _
  refine ⟨B + Real.log 3, ⌈Real.exp (2 * B + Real.log 3)⌉₊, Nat.ceil_pos.mpr hexp, ?_⟩
  have hK0 : (0 : ℝ) < ⌈Real.exp (2 * B + Real.log 3)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr hexp
  have hlogK : 2 * B + Real.log 3 ≤ Real.log ⌈Real.exp (2 * B + Real.log 3)⌉₊ :=
    (Real.le_log_iff_exp_le hK0).mpr (Nat.le_ceil _)
  rintro u (hu | hu)
  · by_contra h
    have := hsupp _ h
    rw [abs_le] at this
    linarith [this.1]
  · by_contra h
    have := hsupp _ h
    rw [abs_le] at this
    linarith [this.2]

/-- **The inequality of Castelnuovo and Severi on the degree points is the Riemann hypothesis.**
RH holds iff for every packet `f ∈ C²_c` supported in a window `[log 3, log K]` the limit of the
pairing of the degree points (jets, contacts and counterterm) is at most the pole term. -/
theorem riemannHypothesis_iff_degreePairing_le_pole :
    RiemannHypothesis ↔
      ∀ (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (K : ℕ), 1 ≤ K →
        (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
        ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N)
            atTop (𝓝 l) →
          l ≤ (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re := by
  constructor
  · intro hRH f hf hfc K hK hsupp l hl
    have hlim := tendsto_degreeForm_add_contacts hf hfc hK hsupp
    have hpos : 0 ≤ (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
        (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re :=
      _root_.RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH f hf hfc
    rw [tendsto_nhds_unique hl hlim]
    linarith
  · intro h
    refine _root_.RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mpr
      fun g hg hgc => ?_
    obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
    have hg' : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
    have hgc' : HasCompactSupport fun u => g (u - s) :=
      hgc.comp_homeomorph (Homeomorph.subRight s)
    have hlim := tendsto_degreeForm_add_contacts hg' hgc' hK hsupp
    have hle := h _ hg' hgc' K hK hsupp _ hlim
    have hfull : (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
          (EF.weilTest (packetTest (fun u => g (u - s)) hg' hgc').1
            (packetTest (fun u => g (u - s)) hg' hgc').1)).re =
        (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
          (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re :=
      congrArg (fun k => (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ)) k).re)
        (weilTest_packet_translate g s)
    rw [← hfull]
    linarith

/-- The pole term of a real packet is twice the product of its two degrees. -/
theorem weilPoleTerm_packet {f : ℝ → ℝ} (hcont : Continuous f) (hfc : HasCompactSupport f) :
    (_root_.RHTower.weilPoleTerm
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) :=
  _root_.RHTower.WeilPoleWeight.re_pole_weilTest_ofReal hcont hfc

/-- **The Riemann hypothesis as the inequality `D·D ≤ 2 d₁ d₂` on the degree points.** RH holds
iff for every packet `f ∈ C²_c` supported in a window `[log 3, log K]` the limit of the pairing of
the degree points is at most twice the product of the degrees `∫ f e^{−u/2}` and `∫ f e^{u/2}`. -/
theorem riemannHypothesis_iff_degreePairing_le_degrees :
    RiemannHypothesis ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
        (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
        ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N)
            atTop (𝓝 l) →
          l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) := by
  rw [riemannHypothesis_iff_degreePairing_le_pole]
  refine forall_congr' fun f => ⟨fun h hf hfc K hK hs l hl => ?_, fun h hf hfc K hK hs l hl => ?_⟩
  · have e : (_root_.RHTower.weilPoleTerm
          (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re =
        2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) :=
      weilPoleTerm_packet hf.continuous hfc
    rw [← e]
    exact h hf hfc K hK hs l hl
  · have e : (_root_.RHTower.weilPoleTerm
          (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re =
        2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) :=
      weilPoleTerm_packet hf.continuous hfc
    rw [e]
    exact h hf hfc K hK hs l hl

/-! ### The sign on short packets -/

/-- The autocorrelation of a packet supported in an interval of length `L` vanishes beyond `L`. -/
theorem packetAutocorr_eq_zero_of_width {f : ℝ → ℝ} {a L x : ℝ}
    (hshort : ∀ u ∉ Set.Ioo a (a + L), f u = 0) (hx : L ≤ x) : packetAutocorr f x = 0 := by
  have h0 : ∀ u : ℝ, f u * f (u + x) = 0 := by
    intro u
    by_cases hu : u ∈ Set.Ioo a (a + L)
    · have hux : u + x ∉ Set.Ioo a (a + L) := fun h => by linarith [hu.1, h.2]
      rw [hshort _ hux, mul_zero]
    · rw [hshort u hu, zero_mul]
  simp [packetAutocorr, h0]

/-- **No contact enters a short packet, and Weil's functional is nonnegative on it.** For a
nonnegative packet supported in an interval of length at most `12/25 < log 2`, Weil's functional
is its pole and archimedean part, and it is nonnegative. -/
theorem weilFullFunctional_packet_nonneg_of_short {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {a L : ℝ} (hL : L ≤ 12 / 25)
    (hshort : ∀ u ∉ Set.Ioo a (a + L), f u = 0) :
    0 ≤ (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have hlog2 : (12 : ℝ) / 25 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hQ : ∀ n : ℕ, 1 < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_width hshort (by
      have h2 : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      linarith)
  have hg : ContDiff ℝ 2 fun u => f (u - -a) := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => f (u - -a) :=
    hfc.comp_homeomorph (Homeomorph.subRight (-a))
  have hpos :=
    _root_.RHTower.WeilLevyQuarterHarmonicDoubling.weilArchRe_nonneg_of_support_Ioo_le_twelve_twenty_fifths
      hg hgc (fun u => hf0 _) hL (fun u hu => hshort _ fun h =>
        hu ⟨by linarith [h.1], by linarith [h.2]⟩)
  rw [weilTest_packet_translate f (-a)] at hpos
  rw [re_weilFullFunctional_packet f hQ, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty,
    mul_zero, sub_zero]
  exact hpos

/-- **The inequality of Castelnuovo and Severi on short packets.** For a nonnegative packet of
width at most `12/25` the pairing of the degree points has a limit, and it is at most the pole
term. -/
theorem tendsto_degreePairing_le_pole_of_short {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {a L : ℝ} (hL : L ≤ 12 / 25)
    (hshort : ∀ u ∉ Set.Ioo a (a + L), f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N)
        atTop (𝓝 l) ∧
      l ≤ (_root_.RHTower.weilPoleTerm
        (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re := by
  have h : 0 ≤ (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ))
      (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re :=
    weilFullFunctional_packet_nonneg_of_short hf hfc hf0 hL hshort
  exact ⟨_, tendsto_degreeForm_add_contacts hf hfc hK hsupp, by linarith⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
