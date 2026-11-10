import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSignIsCarriedByTheContacts
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePacketsOnTheCombOfSquaresCarryWeilsArchimedeanForm

/-!
# On its own comb the system of the squares fails Bézout

On the comb of the integers every system of contact weights other than `Λ` fails Bézout. An
integer-norm system has its own comb: the norms of its elements, with their own density. This
file computes the pairing of one such system on its own comb.

The system of the squares has one generalized prime of norm `p²` for each prime `p`. Its
elements have the norms `n²`, its zeta function is `ζ(2s)`, whose zeros lie on the line
`Re s = ¼` iff the Riemann hypothesis holds, and its von Mangoldt function is `2Λ(k)` at `k²`
(`squareSystemWeight`). Its own comb is the comb of squares: the degree points `n²` with the
masses `2/n` of their cells, the jets between the norms, and the counterterm `log(n/4π)` of
its density.

* **The pairing on the own comb** (`squareContact`, `tendsto_squareForm_add_squareContact`).
  Jets, counterterm and twice the contacts of the system tend, on a packet `F` in the
  logarithmic coordinate of the norms, to `2 d₁ d₂ − Re W_w(F ⋆ F̃)`, where `W_w` is the
  functional of the weights `w` of the system on the comb of the integers. The comb enters
  through its density, which the counterterm removes; what is left is the comb of the integers
  with the contacts of the system.
* **Bézout fails** (`not_weilPositiveFull_squareSystemWeight`, `exists_packet_squarePairing_gt`).
  The weight of the system at `2` is `0` and not `log 2`, so its functional is not positive,
  and some packet has a pairing above `2 d₁ d₂`.

So Bézout on the own comb does not hold whenever the zeros lie on a line: the zeros of `ζ(2s)`
lie on one line with those of `ζ`, and the inequality fails without hypothesis. The jets of a
comb are those of the archimedean factor of `ζ` in the coordinate of the norms; they do not
follow the system.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {g : ℝ → ℝ}

/-! ### The system of the squares -/

/-- The von Mangoldt function of the system of the squares: `2Λ(k)` at the norm `k²`, zero at
the integers that are not squares. -/
def squareSystemWeight (n : ℕ) : ℝ := if IsSquare n then 2 * Λ (Nat.sqrt n) else 0

theorem squareSystemWeight_sq (k : ℕ) : squareSystemWeight (k ^ 2) = 2 * Λ k := by
  rw [squareSystemWeight, if_pos ⟨k, sq k⟩, Nat.sqrt_eq']

theorem squareSystemWeight_two : squareSystemWeight 2 = 0 := by
  have h2 : ¬ IsSquare 2 := by
    rintro ⟨r, hr⟩
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · nlinarith
  rw [squareSystemWeight, if_neg h2]

/-- The contacts of the system on its own comb: the points `m²` and `(mk)²` meet with the
weight `2Λ(k)/k`, and a contact carries the mass `2/m` of its lower point. -/
def squareContact (g : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 L, 2 * Λ k / k *
    ∑ m ∈ Ioc N (N + L * N), degreeSample g N m * degreeSample g N (m * k) * (2 / m)

theorem squareContact_eq (g : ℝ → ℝ) (L N : ℕ) :
    squareContact g L N = weightedContact (fun k => 4 * Λ k / Real.sqrt k) g L N := by
  unfold squareContact weightedContact
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hw : 4 * Λ k / Real.sqrt k / Real.sqrt k = 4 * Λ k / k := by
    rw [div_div, Real.mul_self_sqrt hk0]
  show 2 * Λ k / k * _ = 4 * Λ k / Real.sqrt k / Real.sqrt k * _
  rw [hw, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- The autocorrelation of a packet in the coordinate of the squares, at twice the lag. -/
theorem packetAutocorr_comp_div_two (g : ℝ → ℝ) (x : ℝ) :
    packetAutocorr (fun s => g (s / 2)) (2 * x) = 2 * packetAutocorr g x := by
  unfold packetAutocorr
  have e : ∀ s : ℝ, g (s / 2) * g ((s + 2 * x) / 2) = g (s / 2) * g (s / 2 + x) := fun s => by
    rw [add_div, mul_div_cancel_left₀ x two_ne_zero]
  calc ∫ s, g (s / 2) * g ((s + 2 * x) / 2)
      = ∫ s, g (s / 2) * g (s / 2 + x) := integral_congr_ae (Eventually.of_forall e)
    _ = |(2 : ℝ)| • ∫ u, g u * g (u + x) :=
        Measure.integral_comp_div (fun u : ℝ => g u * g (u + x)) 2
    _ = 2 * ∫ u, g u * g (u + x) := by rw [abs_two, smul_eq_mul]

/-- The contacts of the system on the comb of the integers are those on the comb of squares:
only the squares carry a weight. -/
theorem sum_squareSystemWeight (g : ℝ → ℝ) (K : ℕ) :
    ∑ n ∈ Icc 2 (9 * K ^ 2), squareSystemWeight n / Real.sqrt n *
        packetAutocorr (fun s => g (s / 2)) (Real.log n) =
      ∑ k ∈ Icc 2 (3 * K), 4 * Λ k / k * packetAutocorr g (Real.log k) := by
  classical
  have hT : (Icc 2 (3 * K)).image (fun k => k ^ 2) ⊆ Icc 2 (9 * K ^ 2) := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hk' := Finset.mem_Icc.mp hk
    refine Finset.mem_Icc.mpr ⟨by nlinarith [hk'.1], ?_⟩
    calc k ^ 2 ≤ (3 * K) ^ 2 := Nat.pow_le_pow_left hk'.2 2
      _ = 9 * K ^ 2 := by ring
  rw [← Finset.sum_subset hT fun n hn hnT => ?_]
  · rw [Finset.sum_image fun a _ b _ h => Nat.pow_left_injective two_ne_zero h]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [squareSystemWeight_sq, Nat.cast_pow, Real.sqrt_sq hk0, Real.log_pow, Nat.cast_ofNat,
      packetAutocorr_comp_div_two]
    ring
  · -- an integer of the range that is not the square of some `k ≤ 3K` is not a square
    have hn' := Finset.mem_Icc.mp hn
    have hns : ¬ IsSquare n := by
      rintro ⟨r, rfl⟩
      refine hnT (Finset.mem_image.mpr ⟨r, Finset.mem_Icc.mpr ⟨?_, ?_⟩, sq r⟩)
      · by_contra h2
        have hr : r ≤ 1 := by omega
        have : r * r ≤ 1 := by nlinarith
        omega
      · by_contra h3
        have hr : 3 * K + 1 ≤ r := by omega
        have : (3 * K + 1) * (3 * K + 1) ≤ r * r := Nat.mul_le_mul hr hr
        nlinarith [hn'.2]
    rw [squareSystemWeight, if_neg hns, zero_div, zero_mul]

/-! ### The pairing on the own comb -/

/-- **The pairing of the system of the squares on its own comb.** Jets, the counterterm
`log(n/4π)` and twice the contacts of the system tend, on the packet `F(s) = g(s/2)` in the
coordinate of the norms, to `2 d₁ d₂` minus the functional of the weights of the system on the
comb of the integers. -/
theorem tendsto_squareForm_add_squareContact (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g u = 0) :
    Tendsto (fun N : ℕ => squareForm g (3 * K) N + 2 * squareContact g (3 * K) N) atTop
      (𝓝 (2 * ((∫ s, g (s / 2) * Real.exp (-s / 2)) * ∫ s, g (s / 2) * Real.exp (s / 2)) -
        (_root_.RHTower.weilFullFunctional squareSystemWeight
          (EF.weilTest (fun s => ((g (s / 2) : ℝ) : ℂ)) (fun s => ((g (s / 2) : ℝ) : ℂ)))).re)) := by
  have hF := contDiff_comp_div_two hg
  have hFc := hasCompactSupport_comp_div_two hgc
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hL3 : 1 ≤ 3 * K := by omega
  have hsuppW := window_of_support hK hsupp
  have hK2 : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
  -- the packet in the coordinate of the norms lies in the window of `K²`
  have hsuppF : ∀ s, s ≤ Real.log 3 ∨ Real.log ((K ^ 2 : ℕ) : ℝ) ≤ s → g (s / 2) = 0 := by
    intro s hs
    refine hsupp _ ?_
    rcases hs with h | h
    · exact Or.inl (by linarith)
    · rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h
      exact Or.inr (by linarith)
  have hsuppFW := window_of_support hK2 hsuppF
  have hQ : ∀ n : ℕ, 9 * K ^ 2 < n →
      packetAutocorr (fun s => g (s / 2)) (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_window hδ hsuppFW (Real.log_le_log (by positivity) (by
      have h1 : ((9 * K ^ 2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
      have h2 : ((3 * K ^ 2 : ℕ) : ℝ) ≤ ((9 * K ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast (by nlinarith : 3 * K ^ 2 ≤ 9 * K ^ 2)
      linarith))
  have hfull := re_weilFullFunctional_packet_of_weight squareSystemWeight
    (fun s => g (s / 2)) hQ
  have hpole := weilPoleTerm_packet hF.continuous hFc
  -- the two limits
  have h1 : Tendsto (squareForm g (3 * K)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (fun s => ((g (s / 2) : ℝ) : ℂ)) (fun s => ((g (s / 2) : ℝ) : ℂ))) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (fun s => ((g (s / 2) : ℝ) : ℂ))
              (fun s => ((g (s / 2) : ℝ) : ℂ)))).re))) :=
    tendsto_squareForm hg hgc hK hsupp
  have h2 := (tendsto_weightedContact (fun k => 4 * Λ k / Real.sqrt k) hg.continuous hL3).const_mul 2
  have hsumW : ∑ k ∈ Icc 2 (3 * K), (fun k : ℕ => 4 * Λ k / Real.sqrt k) k / Real.sqrt k *
        ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), g u * g (u + Real.log k) =
      ∑ k ∈ Icc 2 (3 * K), 4 * Λ k / k * packetAutocorr g (Real.log k) :=
    Finset.sum_congr rfl fun k _ => by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [packetAutocorr_eq_integral_window hδ hsuppW]
      show 4 * Λ k / Real.sqrt k / Real.sqrt k * _ = _
      rw [div_div, Real.mul_self_sqrt hk0]
  have hlim := h1.add h2
  rw [hsumW] at hlim
  have e : 2 * ((∫ s, g (s / 2) * Real.exp (-s / 2)) * ∫ s, g (s / 2) * Real.exp (s / 2)) -
        (_root_.RHTower.weilFullFunctional squareSystemWeight
          (EF.weilTest (fun s => ((g (s / 2) : ℝ) : ℂ)) (fun s => ((g (s / 2) : ℝ) : ℂ)))).re =
      -(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (fun s => ((g (s / 2) : ℝ) : ℂ)) (fun s => ((g (s / 2) : ℝ) : ℂ))) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (fun s => ((g (s / 2) : ℝ) : ℂ))
              (fun s => ((g (s / 2) : ℝ) : ℂ)))).re) +
        2 * ∑ k ∈ Icc 2 (3 * K), 4 * Λ k / k * packetAutocorr g (Real.log k) := by
    rw [hfull, sum_squareSystemWeight, hpole]
    ring
  rw [e]
  refine hlim.congr fun N => ?_
  rw [squareContact_eq]

/-! ### Bézout fails -/

/-- The functional of the weights of the system of the squares is not positive: the weight at
`2` is not `log 2`. -/
theorem not_weilPositiveFull_squareSystemWeight :
    ¬ _root_.RHTower.WeilPositiveFull squareSystemWeight := by
  intro h
  have h2 := (_root_.RHTower.WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
    h).2 2 le_rfl
  rw [squareSystemWeight_two, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h2
  exact (Real.log_pos one_lt_two).ne' h2.symm

/-- **On its own comb the system of the squares fails Bézout.** Some packet in a window has a
pairing, with the jets and the counterterm of the comb of squares and the contacts of the
system, whose limit exceeds twice the product of its degrees. -/
theorem exists_packet_squarePairing_gt :
    ∃ (g : ℝ → ℝ) (K : ℕ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ 1 ≤ K ∧
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g u = 0) ∧
      ∃ l : ℝ, Tendsto (fun N : ℕ => squareForm g (3 * K) N + 2 * squareContact g (3 * K) N)
          atTop (𝓝 l) ∧
        2 * ((∫ s, g (s / 2) * Real.exp (-s / 2)) * ∫ s, g (s / 2) * Real.exp (s / 2)) < l := by
  -- a real test on which the functional of the system is negative
  obtain ⟨g₀, hg₀, hg₀c, hneg⟩ : ∃ g₀ : ℝ → ℝ, ContDiff ℝ 2 g₀ ∧ HasCompactSupport g₀ ∧
      (_root_.RHTower.weilFullFunctional squareSystemWeight
        (EF.weilTest (fun u => (g₀ u : ℂ)) (fun u => (g₀ u : ℂ)))).re < 0 := by
    by_contra hcon
    push Not at hcon
    exact not_weilPositiveFull_squareSystemWeight
      (_root_.RHTower.WeilSpectral.weilPositiveFull_of_real fun g₀ hg₀ hg₀c => hcon g₀ hg₀ hg₀c)
  -- move it into a window, in the coordinate of the norms
  obtain ⟨s, K₀, hK₀, hsupp₀⟩ := exists_translate_window hg₀c
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hK₀' : (1 : ℝ) ≤ K₀ := by exact_mod_cast hK₀
  have hlogK : Real.log ((3 * K₀ : ℕ) : ℝ) = Real.log 3 + Real.log K₀ := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
  set t : ℝ := s + Real.log 3 with ht
  have hF1 : ContDiff ℝ 2 fun x => g₀ (x - t) := hg₀.comp (contDiff_id.sub contDiff_const)
  have hF1c : HasCompactSupport fun x => g₀ (x - t) :=
    hg₀c.comp_homeomorph (Homeomorph.subRight t)
  have hgd : ContDiff ℝ 2 fun u : ℝ => g₀ (2 * u - t) :=
    hg₀.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hgc : HasCompactSupport fun u : ℝ => g₀ (2 * u - t) := by
    have h := hF1c.comp_homeomorph (Homeomorph.mulLeft₀ (2 : ℝ) two_ne_zero)
    exact h
  have hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log ((3 * K₀ : ℕ) : ℝ) ≤ u → g₀ (2 * u - t) = 0 := by
    intro u hu
    have e : 2 * u - t = (2 * u - Real.log 3) - s := by rw [ht]; ring
    rw [e]
    refine hsupp₀ _ ?_
    rcases hu with h | h
    · exact Or.inl (by linarith)
    · rw [hlogK] at h
      exact Or.inr (by linarith [Real.log_nonneg hK₀'])
  have hlim := tendsto_squareForm_add_squareContact hgd hgc (by omega : 1 ≤ 3 * K₀) hsupp
  refine ⟨fun u => g₀ (2 * u - t), 3 * K₀, hgd, hgc, by omega, hsupp, _, hlim, ?_⟩
  -- in the coordinate of the norms the packet is a translate of the test
  have hfun : (fun x : ℝ => ((g₀ (2 * (x / 2) - t) : ℝ) : ℂ)) =
      fun x => ((g₀ (x - t) : ℝ) : ℂ) := by
    funext x
    rw [mul_div_cancel₀ x two_ne_zero]
  have hW : (_root_.RHTower.weilFullFunctional squareSystemWeight
        (EF.weilTest (fun x : ℝ => ((g₀ (2 * (x / 2) - t) : ℝ) : ℂ))
          (fun x : ℝ => ((g₀ (2 * (x / 2) - t) : ℝ) : ℂ)))).re =
      (_root_.RHTower.weilFullFunctional squareSystemWeight
        (EF.weilTest (fun u => (g₀ u : ℂ)) (fun u => (g₀ u : ℂ)))).re := by
    rw [hfun]
    exact congrArg (fun k => (_root_.RHTower.weilFullFunctional squareSystemWeight k).re)
      (weilTest_packet_translate g₀ t)
  rw [hW]
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
