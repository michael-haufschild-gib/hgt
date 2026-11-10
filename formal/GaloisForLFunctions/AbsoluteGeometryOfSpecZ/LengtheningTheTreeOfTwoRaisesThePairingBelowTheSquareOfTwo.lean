import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTreeOfAPrimeIsGluedAlongTheCombWithTheLengthLogP
import GaloisForLFunctions.SelectiveArithmetic.EveryVisibleWeightIsBoundedByTheMass

/-!
# Lengthening the tree of two raises the pairing below the square of two

The edge length `ℓ` of the tree of a prime `p`, glued along the comb, is a parameter of the
pairing of the degree points. On packets of length at most `2 log p` only the first point of
each chain is seen, and the functional of the glued tree is affine in the length:
`Z(f) + (ℓ − log p)·E_p(f)` with the generator
`E_p(f) = ∫f²/(p − 1) − (2/√p)·h_f(log p)`: the mean of the Busemann function minus the contact
of `p` on the autocorrelation `h_f`.

* **The generator** (`pairForm_treeDeviation_eq`, `treeGenerator_ge`, `treeGenerator_two_ge`):
  on packets of length at most `2 log p`, `E_p ≥ (1/(p − 1) − 1/√p) ∫f²`. The constant is
  positive for `p = 2` only: `E_2 ≥ (1 − 1/√2) ∫f²` on packets of length at most `log 4`.
* **A Lefschetz path for the prime `2`** (`treeBezoutAt_two_mono`, `exists_treeBezoutAt_two`,
  `exists_not_treeBezoutAt_two`, `exists_treeThreshold_two`): on packets of length `L ≤ log 4`
  a longer tree has a larger functional; all long trees satisfy Bézout, without hypothesis; all
  short ones fail; so Bézout holds exactly from a threshold length `ℓ*(L)` on.
* **The square** (`treeBezoutAt_two_of_width`): for `L ≤ 181/250` the threshold is at most
  `log 2 − 1/10000`. Bézout for the square of the integers on packets of length `L ≤ log 4` is
  the statement `ℓ*(L) ≤ log 2`.
* **Odd primes** (`exists_packet_treeGenerator_neg`, `exists_not_treeBezoutAt_of_three_le`): for
  `p ≥ 3` the generator is negative on a pair of bumps at the distance `log p`, and on packets
  of any length above `log p` every long tree of `p` fails.

So the length of the tree of `2` is a deformation of the pairing with a positive generator, a
base point where the inequality holds without hypothesis, and one point of degeneration, as long
as the second point `4` of the chains of `2` is not seen. Beyond the length `log 4`, and for
every other prime, the generator is indefinite; on all packets the only length that is not
refuted is `log p` (`treeBezout_iff`).
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {f : ℝ → ℝ}

/-! ### The autocorrelation of a packet of a given length -/

/-- The autocorrelation of a packet of length `L` vanishes at displacements `≥ L`. -/
theorem packetAutocorr_eq_zero_of_length {x₀ L : ℝ}
    (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) {x : ℝ} (hx : L ≤ x) :
    packetAutocorr f x = 0 := by
  have h0 : ∀ u : ℝ, f u * f (u + x) = 0 := fun u => by
    by_cases hu : u ≤ x₀
    · rw [hlen u (Or.inl hu), zero_mul]
    · rw [hlen (u + x) (Or.inr (by linarith [not_le.mp hu])), mul_zero]
  simp [packetAutocorr, h0]

/-- **At a displacement of at least half the length the autocorrelation is at most half the
mass**: the two factors live on disjoint halves of the packet. -/
theorem two_mul_abs_packetAutocorr_le_of_length (hf : Continuous f) (hfc : HasCompactSupport f)
    {x₀ L y : ℝ} (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) (hy : L ≤ 2 * y) :
    2 * |packetAutocorr f y| ≤ ∫ u, f u ^ 2 := by
  have hgsq : Integrable fun u => f u ^ 2 := by
    refine ((hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show f u * f u = f u ^ 2
    ring
  have hI1 : Integrable (Set.indicator (Set.Iio (x₀ + y)) fun u => f u ^ 2) :=
    hgsq.indicator measurableSet_Iio
  have hI2 : Integrable (Set.indicator (Set.Ioi (x₀ + y)) fun u => f u ^ 2) :=
    hgsq.indicator measurableSet_Ioi
  have hI2s : Integrable fun u => Set.indicator (Set.Ioi (x₀ + y)) (fun x => f x ^ 2) (u + y) :=
    hI2.comp_add_right y
  have hprod : Integrable fun u => 2 * |f u * f (u + y)| :=
    (((hf.mul (hf.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hfc.mul_right).abs).const_mul 2
  have hpt : ∀ u, 2 * |f u * f (u + y)| ≤
      Set.indicator (Set.Iio (x₀ + y)) (fun x => f x ^ 2) u +
        Set.indicator (Set.Ioi (x₀ + y)) (fun x => f x ^ 2) (u + y) := by
    intro u
    by_cases h0 : f u * f (u + y) = 0
    · rw [h0, abs_zero, mul_zero]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
        (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
    · have h1 : f u ≠ 0 := left_ne_zero_of_mul h0
      have h2 : f (u + y) ≠ 0 := right_ne_zero_of_mul h0
      have hu1 : x₀ < u := by
        by_contra hcon
        exact h1 (hlen u (Or.inl (not_lt.mp hcon)))
      have hu2 : u + y < x₀ + L := by
        by_contra hcon
        exact h2 (hlen (u + y) (Or.inr (not_lt.mp hcon)))
      rw [Set.indicator_of_mem (show u ∈ Set.Iio (x₀ + y) from by
          rw [Set.mem_Iio]
          linarith),
        Set.indicator_of_mem (show u + y ∈ Set.Ioi (x₀ + y) from by
          rw [Set.mem_Ioi]
          linarith), abs_mul, ← mul_assoc]
      have h := two_mul_le_add_sq |f u| |f (u + y)|
      rwa [sq_abs, sq_abs] at h
  have hsum : ∀ u, Set.indicator (Set.Iio (x₀ + y)) (fun x => f x ^ 2) u +
      Set.indicator (Set.Ioi (x₀ + y)) (fun x => f x ^ 2) u ≤ f u ^ 2 := by
    intro u
    rcases lt_trichotomy u (x₀ + y) with h | h | h
    · rw [Set.indicator_of_mem (show u ∈ Set.Iio (x₀ + y) from h),
        Set.indicator_of_notMem (show u ∉ Set.Ioi (x₀ + y) from not_lt.mpr h.le), add_zero]
    · rw [Set.indicator_of_notMem (show u ∉ Set.Iio (x₀ + y) from not_lt.mpr h.ge),
        Set.indicator_of_notMem (show u ∉ Set.Ioi (x₀ + y) from not_lt.mpr h.le), add_zero]
      exact sq_nonneg _
    · rw [Set.indicator_of_notMem (show u ∉ Set.Iio (x₀ + y) from not_lt.mpr h.le),
        Set.indicator_of_mem (show u ∈ Set.Ioi (x₀ + y) from h), zero_add]
  have hint : ∫ u, 2 * |f u * f (u + y)| ≤
      ∫ u, (Set.indicator (Set.Iio (x₀ + y)) (fun x => f x ^ 2) u +
        Set.indicator (Set.Ioi (x₀ + y)) (fun x => f x ^ 2) (u + y)) :=
    integral_mono hprod (hI1.add hI2s) hpt
  rw [integral_add hI1 hI2s,
    integral_add_right_eq_self (fun u => Set.indicator (Set.Ioi (x₀ + y)) (fun x => f x ^ 2) u) y,
    integral_const_mul] at hint
  have h2 : (∫ u, Set.indicator (Set.Iio (x₀ + y)) (fun x => f x ^ 2) u) +
      ∫ u, Set.indicator (Set.Ioi (x₀ + y)) (fun x => f x ^ 2) u ≤ ∫ u, f u ^ 2 := by
    rw [← integral_add hI1 hI2]
    exact integral_mono (hI1.add hI2) hgsq hsum
  have h3 : |packetAutocorr f y| ≤ ∫ u, |f u * f (u + y)| := abs_integral_le_integral_abs
  linarith

/-! ### The generator of the length of a tree -/

/-- The generator of the length of the tree of `p` on packets that see one point of each chain:
the mean of the Busemann function minus the contact of `p`. -/
def treeGenerator (p : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∫ u, f u ^ 2) / ((p : ℝ) - 1) - 2 / Real.sqrt p * packetAutocorr f (Real.log p)

/-- **The functional of a glued tree is affine in its length** on packets of length at most
`2 log p`. -/
theorem pairForm_treeDeviation_eq {p : ℕ} (hp : p.Prime) (t : ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {x₀ L : ℝ} (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0)
    (hL : L ≤ 2 * Real.log p) :
    pairForm (treeDeviation p t) (t / ((p : ℝ) - 1)) f = zeroSum f + t * treeGenerator p f := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hQ : ∀ n : ℕ, p * p < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_length hlen (by
      have h1 : ((p * p : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.le
      have h2 : Real.log ((p * p : ℕ) : ℝ) ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast Nat.mul_pos hp.pos hp.pos) h1
      rw [Nat.cast_mul, Real.log_mul hp0.ne' hp0.ne'] at h2
      linarith)
  have h1 := re_weilFullFunctional_packet_of_weight
    (fun n => (Λ n : ℝ) + treeDeviation p t n) f hQ
  have h2 := re_weilFullFunctional_packet_of_weight (fun n => (Λ n : ℝ)) f hQ
  have hz := zeroSum_eq_weilFullFunctional hf hfc
  -- of the deviation only the contact at `p` is seen
  have hdev : ∑ k ∈ Icc 2 (p * p),
      treeDeviation p t k / Real.sqrt k * packetAutocorr f (Real.log k) =
      t / Real.sqrt p * packetAutocorr f (Real.log p) := by
    rw [Finset.sum_eq_single p]
    · rw [treeDeviation_self]
    · intro k _ hkp
      by_cases hk : ∃ j : ℕ, k = p ^ (j + 1)
      · obtain ⟨j, rfl⟩ := hk
        have hj : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with rfl | h
          · exact absurd (by simp) hkp
          · exact h
        have hA : packetAutocorr f (Real.log ((p ^ (j + 1) : ℕ) : ℝ)) = 0 :=
          packetAutocorr_eq_zero_of_length hlen (by
            rw [Nat.cast_pow, Real.log_pow]
            have h2j : (2 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ j + 1)
            have := mul_le_mul_of_nonneg_right h2j hlogp.le
            linarith)
        rw [hA, mul_zero]
      · rw [treeDeviation, if_neg hk, zero_div, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_mul_self p⟩) hnot
  have hsplit : ∑ k ∈ Icc 2 (p * p),
        ((Λ k : ℝ) + treeDeviation p t k) / Real.sqrt k * packetAutocorr f (Real.log k) =
      ∑ k ∈ Icc 2 (p * p), (Λ k : ℝ) / Real.sqrt k * packetAutocorr f (Real.log k) +
        ∑ k ∈ Icc 2 (p * p),
          treeDeviation p t k / Real.sqrt k * packetAutocorr f (Real.log k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold pairForm treeGenerator
  rw [h1, hsplit, hdev, hz, h2]
  ring

/-- **The generator is bounded by the mass** on packets of length at most `2 log p`. -/
theorem treeGenerator_ge (hf : Continuous f) (hfc : HasCompactSupport f) {p : ℕ} (hp : p.Prime)
    {x₀ L : ℝ} (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) (hL : L ≤ 2 * Real.log p) :
    (1 / ((p : ℝ) - 1) - 1 / Real.sqrt p) * (∫ u, f u ^ 2) ≤ treeGenerator p f ∧
      treeGenerator p f ≤ (1 / ((p : ℝ) - 1) + 1 / Real.sqrt p) * ∫ u, f u ^ 2 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have h := two_mul_abs_packetAutocorr_le_of_length hf hfc hlen hL
  have hA := abs_le.mp (show |packetAutocorr f (Real.log p)| ≤ (∫ u, f u ^ 2) / 2 by linarith)
  have hc : (0 : ℝ) ≤ 2 / Real.sqrt p := by positivity
  have h1 := mul_le_mul_of_nonneg_left hA.2 hc
  have h2 := mul_le_mul_of_nonneg_left hA.1 hc
  have e1 : 2 / Real.sqrt p * ((∫ u, f u ^ 2) / 2) = 1 / Real.sqrt p * ∫ u, f u ^ 2 := by ring
  have e2 : 2 / Real.sqrt p * -((∫ u, f u ^ 2) / 2) = -(1 / Real.sqrt p * ∫ u, f u ^ 2) := by
    ring
  rw [e1] at h1
  rw [e2] at h2
  unfold treeGenerator
  constructor
  · have e : (1 / ((p : ℝ) - 1) - 1 / Real.sqrt p) * (∫ u, f u ^ 2) =
        (∫ u, f u ^ 2) / ((p : ℝ) - 1) - 1 / Real.sqrt p * ∫ u, f u ^ 2 := by ring
    rw [e]
    linarith
  · have e : (1 / ((p : ℝ) - 1) + 1 / Real.sqrt p) * (∫ u, f u ^ 2) =
        (∫ u, f u ^ 2) / ((p : ℝ) - 1) + 1 / Real.sqrt p * ∫ u, f u ^ 2 := by ring
    rw [e]
    linarith

theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- **The generator of the tree of `2` is positive** on packets of length at most `log 4`. -/
theorem treeGenerator_two_ge (hf : Continuous f) (hfc : HasCompactSupport f) {x₀ L : ℝ}
    (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) (hL : L ≤ 2 * Real.log 2) :
    (1 - 1 / Real.sqrt 2) * (∫ u, f u ^ 2) ≤ treeGenerator 2 f ∧
      treeGenerator 2 f ≤ 2 * ∫ u, f u ^ 2 := by
  have h := treeGenerator_ge hf hfc Nat.prime_two hlen (by exact_mod_cast hL)
  have e1 : (1 / (((2 : ℕ) : ℝ) - 1) - 1 / Real.sqrt ((2 : ℕ) : ℝ)) = 1 - 1 / Real.sqrt 2 := by
    norm_num
  have e2 : (1 / (((2 : ℕ) : ℝ) - 1) + 1 / Real.sqrt ((2 : ℕ) : ℝ)) = 1 + 1 / Real.sqrt 2 := by
    norm_num
  rw [e1, e2] at h
  have hM : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hs : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one (by linarith [one_lt_sqrt_two])]
    exact one_lt_sqrt_two.le
  refine ⟨h.1, h.2.trans ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hs hM]

/-! ### Bézout for a glued tree on packets of a given length -/

/-- Bézout for the comb of the integers with the tree of `p` glued with the edge length `ℓ`, on
the packets of length at most `L`: the functional of the pair is nonnegative there. -/
def TreeBezoutAt (p : ℕ) (ℓ L : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
    (∃ x₀ : ℝ, ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → g u = 0) →
    0 ≤ pairForm (treeDeviation p (ℓ - Real.log p)) ((ℓ - Real.log p) / ((p : ℝ) - 1)) g

/-- Bézout at a length is the inequality for the limits of the pairing on the packets of that
length in the windows. -/
theorem treeBezoutAt_iff {p : ℕ} (hp : p.Prime) (ℓ L : ℝ) :
    TreeBezoutAt p ℓ L ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
      (∃ x₀ : ℝ, ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) →
      ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N +
          (Real.log p - ℓ) * busemannMass p f (3 * K) N +
          2 * weightedContact (fun n => (Λ n : ℝ) + treeDeviation p (ℓ - Real.log p) n) f
            (3 * K) N) atTop (𝓝 l) →
        l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) := by
  constructor
  · intro h f hf hfc K hK hsupp hlen l hl
    rw [tendsto_nhds_unique hl (tendsto_treePairing hp ℓ hf hfc hK hsupp)]
    linarith [h f hf hfc hlen]
  · intro h g hg hgc ⟨x₀, hlen⟩
    obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
    have hg' : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
    have hgc' : HasCompactSupport fun u => g (u - s) :=
      hgc.comp_homeomorph (Homeomorph.subRight s)
    have hlen' : ∃ x₁ : ℝ, ∀ u, u ≤ x₁ ∨ x₁ + L ≤ u → g (u - s) = 0 :=
      ⟨x₀ + s, fun u hu => hlen _ (by
        rcases hu with h1 | h1
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith))⟩
    have hle := h _ hg' hgc' K hK hsupp hlen' _ (tendsto_treePairing hp ℓ hg' hgc' hK hsupp)
    rw [pairForm_translate] at hle
    linarith

/-! ### The prime `2`: a monotone path -/

theorem one_div_sqrt_two_lt_one : 1 / Real.sqrt 2 < 1 := by
  rw [div_lt_one (by linarith [one_lt_sqrt_two])]
  exact one_lt_sqrt_two

theorem treeGenerator_two_nonneg (hf : Continuous f) (hfc : HasCompactSupport f) {x₀ L : ℝ}
    (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) (hL : L ≤ 2 * Real.log 2) :
    0 ≤ treeGenerator 2 f :=
  (mul_nonneg (by linarith [one_div_sqrt_two_lt_one])
    (integral_nonneg fun u => sq_nonneg _)).trans (treeGenerator_two_ge hf hfc hlen hL).1

/-- On packets of length at most `log 4`, Bézout for the tree of `2` of length `ℓ` is the
positivity of `Z + (ℓ − log 2)·E₂`. -/
theorem treeBezoutAt_two_iff {L : ℝ} (hL : L ≤ 2 * Real.log 2) (ℓ : ℝ) :
    TreeBezoutAt 2 ℓ L ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∃ x₀ : ℝ, ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → g u = 0) →
      0 ≤ zeroSum g + (ℓ - Real.log 2) * treeGenerator 2 g := by
  have hL' : L ≤ 2 * Real.log ((2 : ℕ) : ℝ) := by exact_mod_cast hL
  unfold TreeBezoutAt
  refine forall₄_congr fun g hg hgc hlen => ?_
  obtain ⟨x₀, hx₀⟩ := hlen
  rw [pairForm_treeDeviation_eq Nat.prime_two _ hg hgc hx₀ hL']
  simp only [Nat.cast_ofNat]

/-- **A longer tree of `2` has a larger functional** on packets of length at most `log 4`. -/
theorem treeBezoutAt_two_mono {L : ℝ} (hL : L ≤ 2 * Real.log 2) {ℓ ℓ' : ℝ} (hℓ : ℓ ≤ ℓ')
    (h : TreeBezoutAt 2 ℓ L) : TreeBezoutAt 2 ℓ' L := by
  rw [treeBezoutAt_two_iff hL] at h ⊢
  intro g hg hgc hlen
  have h0 := h g hg hgc hlen
  obtain ⟨x₀, hx₀⟩ := hlen
  have hE0 := treeGenerator_two_nonneg hg.continuous hgc hx₀ hL
  linarith [mul_le_mul_of_nonneg_right (sub_le_sub_right hℓ (Real.log 2)) hE0]

/-- **Cauchy–Schwarz against a cutoff.** -/
theorem sq_integral_abs_le_of_majorant {g w : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hw : Continuous w) (hwc : HasCompactSupport w)
    (h1 : ∀ u, g u ≠ 0 → w u = 1) :
    (∫ u, |g u|) ^ 2 ≤ (∫ u, w u ^ 2) * ∫ u, g u ^ 2 := by
  have hi1 : Integrable fun u => w u ^ 2 := by
    refine ((hw.mul hw).integrable_of_hasCompactSupport hwc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show w u * w u = w u ^ 2
    ring
  have hi2 : Integrable fun u => |g u| := (hg.integrable_of_hasCompactSupport hgc).abs
  have hi3 : Integrable fun u => g u ^ 2 := by
    refine ((hg.mul hg).integrable_of_hasCompactSupport hgc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show g u * g u = g u ^ 2
    ring
  have key : ∀ t : ℝ, 0 ≤ (∫ u, w u ^ 2) * (t * t) + -(2 * ∫ u, |g u|) * t + ∫ u, g u ^ 2 := by
    intro t
    have hpt : ∀ u, (t * w u - |g u|) ^ 2 = (t * t * w u ^ 2 - 2 * t * |g u|) + g u ^ 2 := by
      intro u
      by_cases h0 : g u = 0
      · rw [h0, abs_zero]
        ring
      · have habs : |g u| ^ 2 = g u ^ 2 := sq_abs _
        rw [h1 u h0, ← habs]
        ring
    have hint : 0 ≤ ∫ u, (t * w u - |g u|) ^ 2 := integral_nonneg fun u => sq_nonneg _
    have ha : Integrable fun u => t * t * w u ^ 2 := hi1.const_mul _
    have hb : Integrable fun u => 2 * t * |g u| := hi2.const_mul _
    have hab : Integrable fun u => t * t * w u ^ 2 - 2 * t * |g u| := ha.sub hb
    rw [funext hpt, integral_add hab hi3, integral_sub ha hb, integral_const_mul,
      integral_const_mul] at hint
    linarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  linarith

/-- **The sum over the zeros is bounded below by the mass on packets of a given length.** -/
theorem exists_zeroSum_ge_of_length (L : ℝ) :
    ∃ C : ℝ, ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∃ x₀ : ℝ, ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) → -(C * ∫ u, f u ^ 2) ≤ zeroSum f := by
  have ha0 : 0 ≤ |L| := abs_nonneg L
  have hcw : Continuous (SelectiveArithmetic.cutoff (|L| + 2) 1) :=
    (SelectiveArithmetic.contDiff_cutoff (|L| + 2) 1).continuous
  have hcwc : HasCompactSupport (SelectiveArithmetic.cutoff (|L| + 2) 1) :=
    SelectiveArithmetic.hasCompactSupport_cutoff (by norm_num)
  refine ⟨2 * (Real.exp |L| * ∫ u, SelectiveArithmetic.cutoff (|L| + 2) 1 u ^ 2) +
    (SelectiveArithmetic.archConstant +
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * |L|)⌋₊, 2 * |(Λ n : ℝ)| / Real.sqrt n),
    fun f hf hfc hlen => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hlen
  -- centre the packet
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -(x₀ + L / 2) := ⟨_, rfl⟩
  have hg : ContDiff ℝ 2 fun u => f (u - s) := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => f (u - s) := hfc.comp_homeomorph (Homeomorph.subRight s)
  have hhalf : L / 2 ≤ |L| := by
    have := le_abs_self L
    linarith
  have hvan : ∀ u, |L| ≤ |u| → f (u - s) = 0 := by
    intro u hu
    rcases le_abs.mp hu with h | h
    · exact hx₀ _ (Or.inr (by rw [hs]; linarith))
    · exact hx₀ _ (Or.inl (by rw [hs]; linarith))
  have hgs : tsupport (fun u => ((f (u - s) : ℝ) : ℂ)) ⊆ Set.Icc (-|L|) |L| := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hne : f (u - s) ≠ 0 := fun h0 =>
      Function.mem_support.mp hu (by rw [h0, Complex.ofReal_zero])
    have hlt : |u| < |L| := lt_of_not_ge fun h => hne (hvan u h)
    exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
  have hGd := contDiff_ofReal_packet hg
  -- the archimedean energy and the contacts are bounded by the mass
  have hfeas : SelectiveArithmetic.Feasible
      (Real.exp (SelectiveArithmetic.archConstant +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * |L|)⌋₊, 2 * |(Λ n : ℝ)| / Real.sqrt n)) |L|
      (fun n => (Λ n : ℝ)) :=
    SelectiveArithmetic.feasible_of_sum_abs_le (Real.log_exp _).ge
  have hsys := hfeas _ hGd hgs
  have e1 := SelectiveArithmetic.systemForm_eq hGd hgs (fun n => (Λ n : ℝ))
    (Real.exp (SelectiveArithmetic.archConstant +
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * |L|)⌋₊, 2 * |(Λ n : ℝ)| / Real.sqrt n))
  have e2 := SelectiveArithmetic.systemForm_eq hGd hgs (fun n => (Λ n : ℝ)) 1
  rw [Real.log_exp] at e1
  rw [Real.log_one, zero_mul, add_zero] at e2
  have e3 : SelectiveArithmetic.systemForm (fun n => (Λ n : ℝ)) 1 |L|
      (fun u => ((f (u - s) : ℝ) : ℂ)) =
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => ((f (u - s) : ℝ) : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * |L|)⌋₊
          (τ / (2 * π)) := by
    unfold SelectiveArithmetic.systemForm
    simp only [Real.log_one, add_zero]
  have hW := re_weilFullFunctional_eq_pole_add_symbol (fun n => (Λ n : ℝ)) hGd hgs
  have hpole := weilPoleTerm_packet hg.continuous hgc
  have hz := zeroSum_eq_weilFullFunctional hg hgc
  have hnorm : (∫ x : ℝ, ‖((f (x - s) : ℝ) : ℂ)‖ ^ 2) = ∫ x, f (x - s) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => by
      show ‖((f (x - s) : ℝ) : ℂ)‖ ^ 2 = f (x - s) ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
  rw [hnorm] at e1
  -- the pole term is bounded by the mass
  have hI : Integrable fun u => |f (u - s)| :=
    (hg.continuous.integrable_of_hasCompactSupport hgc).abs
  have hexp : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) →
      |∫ u, f (u - s) * Real.exp (σ * u / 2)| ≤ Real.exp (|L| / 2) * ∫ u, |f (u - s)| := by
    intro σ hσ
    have hint : Integrable fun u => |f (u - s) * Real.exp (σ * u / 2)| :=
      ((hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right).abs
    calc |∫ u, f (u - s) * Real.exp (σ * u / 2)|
        ≤ ∫ u, |f (u - s) * Real.exp (σ * u / 2)| := abs_integral_le_integral_abs
      _ ≤ ∫ u, Real.exp (|L| / 2) * |f (u - s)| := by
          refine integral_mono hint (hI.const_mul _) fun u => ?_
          show |f (u - s) * Real.exp (σ * u / 2)| ≤ Real.exp (|L| / 2) * |f (u - s)|
          by_cases h0 : f (u - s) = 0
          · rw [h0, zero_mul, abs_zero, mul_zero]
          · have hlt : |u| < |L| := lt_of_not_ge fun h => h0 (hvan u h)
            have hu := abs_lt.mp hlt
            rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
            rcases hσ with rfl | rfl <;> linarith [hu.1, hu.2]
      _ = Real.exp (|L| / 2) * ∫ u, |f (u - s)| := integral_const_mul _ _
  have hd1 : |∫ u, f (u - s) * Real.exp (-u / 2)| ≤
      Real.exp (|L| / 2) * ∫ u, |f (u - s)| := by
    have h := hexp (-1) (Or.inr rfl)
    have e : (fun u : ℝ => f (u - s) * Real.exp (-1 * u / 2)) =
        fun u => f (u - s) * Real.exp (-u / 2) := by
      funext u
      rw [neg_one_mul]
    rwa [e] at h
  have hd2 : |∫ u, f (u - s) * Real.exp (u / 2)| ≤
      Real.exp (|L| / 2) * ∫ u, |f (u - s)| := by
    have h := hexp 1 (Or.inl rfl)
    have e : (fun u : ℝ => f (u - s) * Real.exp (1 * u / 2)) =
        fun u => f (u - s) * Real.exp (u / 2) := by
      funext u
      rw [one_mul]
    rwa [e] at h
  have hCS := sq_integral_abs_le_of_majorant hg.continuous hgc hcw hcwc (fun u hu => by
    have hlt : |u| < |L| := lt_of_not_ge fun h => hu (hvan u h)
    exact SelectiveArithmetic.cutoff_eq_one (by norm_num) (by linarith))
  have hI0 : 0 ≤ ∫ u, |f (u - s)| := integral_nonneg fun u => abs_nonneg _
  have hee : Real.exp (|L| / 2) * Real.exp (|L| / 2) = Real.exp |L| := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : |(∫ u, f (u - s) * Real.exp (-u / 2)) * ∫ u, f (u - s) * Real.exp (u / 2)| ≤
      Real.exp |L| * ((∫ u, SelectiveArithmetic.cutoff (|L| + 2) 1 u ^ 2) *
        ∫ u, f (u - s) ^ 2) := by
    rw [abs_mul]
    calc |∫ u, f (u - s) * Real.exp (-u / 2)| * |∫ u, f (u - s) * Real.exp (u / 2)|
        ≤ (Real.exp (|L| / 2) * ∫ u, |f (u - s)|) * (Real.exp (|L| / 2) * ∫ u, |f (u - s)|) :=
          mul_le_mul hd1 hd2 (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hI0)
      _ = Real.exp |L| * (∫ u, |f (u - s)|) ^ 2 := by
          rw [← hee]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCS (Real.exp_pos _).le
  have hlow := (abs_le.mp hprod).1
  have hmass : ∫ u, f (u - s) ^ 2 = ∫ u, f u ^ 2 :=
    integral_sub_right_eq_self (fun u => f u ^ 2) s
  rw [← zeroSum_translate hf hfc s, hz, hW, hpole, ← e3, ← hmass]
  linarith

/-- **Long trees of `2` satisfy Bézout below the square of `2`, without hypothesis.** -/
theorem exists_treeBezoutAt_two {L : ℝ} (hL : L ≤ 2 * Real.log 2) :
    ∃ ℓ₀ : ℝ, ∀ ℓ, ℓ₀ ≤ ℓ → TreeBezoutAt 2 ℓ L := by
  obtain ⟨C, hC⟩ := exists_zeroSum_ge_of_length L
  have hκ : 0 < 1 - 1 / Real.sqrt 2 := by linarith [one_div_sqrt_two_lt_one]
  refine ⟨Real.log 2 + |C| / (1 - 1 / Real.sqrt 2), fun ℓ hℓ => ?_⟩
  rw [treeBezoutAt_two_iff hL]
  intro g hg hgc hlen
  have hZ := hC g hg hgc hlen
  obtain ⟨x₀, hx₀⟩ := hlen
  have hE := (treeGenerator_two_ge hg.continuous hgc hx₀ hL).1
  have hM : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have ht : |C| / (1 - 1 / Real.sqrt 2) ≤ ℓ - Real.log 2 := by linarith
  have ht0 : 0 ≤ ℓ - Real.log 2 := (div_nonneg (abs_nonneg _) hκ.le).trans ht
  have h2 : |C| ≤ (ℓ - Real.log 2) * (1 - 1 / Real.sqrt 2) := by rwa [div_le_iff₀ hκ] at ht
  -- `t·E ≥ t (1 − 1/√2) M ≥ |C| M`
  have h5 : |C| * (∫ u, g u ^ 2) ≤ (ℓ - Real.log 2) * treeGenerator 2 g :=
    calc |C| * (∫ u, g u ^ 2) ≤ (ℓ - Real.log 2) * (1 - 1 / Real.sqrt 2) * ∫ u, g u ^ 2 :=
          mul_le_mul_of_nonneg_right h2 hM
      _ = (ℓ - Real.log 2) * ((1 - 1 / Real.sqrt 2) * ∫ u, g u ^ 2) := by ring
      _ ≤ (ℓ - Real.log 2) * treeGenerator 2 g := mul_le_mul_of_nonneg_left hE ht0
  have h4 : C * (∫ u, g u ^ 2) ≤ |C| * ∫ u, g u ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hM
  linarith

/-- **Up to the length `181/250` the tree of `2` may be shorter than `log 2`.** -/
theorem treeBezoutAt_two_of_width {L : ℝ} (hL : L ≤ 181 / 250) {ℓ : ℝ}
    (hℓ : Real.log 2 - 1 / 10000 ≤ ℓ) : TreeBezoutAt 2 ℓ L := by
  have hL2 : L ≤ 2 * Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rw [treeBezoutAt_two_iff hL2]
  intro g hg hgc hlen
  obtain ⟨x₀, hx₀⟩ := hlen
  have hZ : 1 / 5000 * ∫ u, g u ^ 2 ≤ zeroSum g :=
    zeroSum_ge_of_width hg hgc (c := x₀ + L / 2) fun u hu => by
      rcases lt_abs.mp hu with h | h
      · exact hx₀ u (Or.inr (by linarith))
      · exact hx₀ u (Or.inl (by linarith))
  have hE := treeGenerator_two_ge hg.continuous hgc hx₀ hL2
  have hE0 := treeGenerator_two_nonneg hg.continuous hgc hx₀ hL2
  have ht : -(1 / 10000) ≤ ℓ - Real.log 2 := by linarith
  have h1 : -(1 / 10000) * treeGenerator 2 g ≤ (ℓ - Real.log 2) * treeGenerator 2 g :=
    mul_le_mul_of_nonneg_right ht hE0
  linarith [hE.2]

/-- **Short trees of `2` fail.** -/
theorem exists_not_treeBezoutAt_two {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 2 * Real.log 2) :
    ∃ ℓ₁ : ℝ, ∀ ℓ, ℓ ≤ ℓ₁ → ¬ TreeBezoutAt 2 ℓ L := by
  have hr : 0 < L / 2 := by positivity
  have hδ : 0 < L / 2 / 2 := by positivity
  -- one bump of length `L`
  have hg : ContDiff ℝ 2 (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2)) :=
    (SelectiveArithmetic.contDiff_cutoff _ _).of_le (by norm_num)
  have hgc := SelectiveArithmetic.hasCompactSupport_cutoff (a := L / 2) hδ
  have hx₀ : ∀ u, u ≤ -(L / 2) ∨ -(L / 2) + L ≤ u →
      SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2) u = 0 := fun u hu =>
    SelectiveArithmetic.cutoff_eq_zero hδ (by
      rcases hu with h | h
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl (by linarith)))
  have hmass : L / 2 ≤ ∫ u, SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2) u ^ 2 := by
    have h := SelectiveArithmetic.le_packetAutocorr_cutoff_zero hr
    have e : packetAutocorr (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2)) 0 =
        ∫ u, SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2) u ^ 2 := by
      rw [packetAutocorr]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2) u *
          SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2) (u + 0) =
        SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2) u ^ 2
      rw [add_zero, sq]
    rwa [e] at h
  have hκ : 0 < 1 - 1 / Real.sqrt 2 := by linarith [one_div_sqrt_two_lt_one]
  have hE := (treeGenerator_two_ge hg.continuous hgc hx₀ hL).1
  have hEpos : 0 < treeGenerator 2 (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2)) :=
    lt_of_lt_of_le (mul_pos hκ (lt_of_lt_of_le hr hmass)) hE
  refine ⟨Real.log 2 - (|zeroSum (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2))| + 1) /
      treeGenerator 2 (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2)), fun ℓ hℓ h => ?_⟩
  have h0 := (treeBezoutAt_two_iff hL ℓ).mp h _ hg hgc ⟨_, hx₀⟩
  have ht : ℓ - Real.log 2 ≤
      -((|zeroSum (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2))| + 1) /
        treeGenerator 2 (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2))) := by linarith
  have h1 := mul_le_mul_of_nonneg_right ht hEpos.le
  rw [neg_mul, div_mul_cancel₀ _ hEpos.ne'] at h1
  linarith [le_abs_self (zeroSum (SelectiveArithmetic.cutoff (L / 2) (L / 2 / 2)))]

/-- **The threshold length.** On packets of length `L`, `0 < L ≤ log 4`, the tree of `2`
satisfies Bézout exactly from one length on. -/
theorem exists_treeThreshold_two {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 2 * Real.log 2) :
    ∃ ℓs : ℝ, ∀ ℓ, TreeBezoutAt 2 ℓ L ↔ ℓs ≤ ℓ := by
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_treeBezoutAt_two hL
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_not_treeBezoutAt_two hL0 hL
  have hne : {ℓ : ℝ | TreeBezoutAt 2 ℓ L}.Nonempty := ⟨ℓ₀, hℓ₀ ℓ₀ le_rfl⟩
  have hbdd : BddBelow {ℓ : ℝ | TreeBezoutAt 2 ℓ L} :=
    ⟨ℓ₁, fun ℓ hℓ => le_of_not_ge fun h => hℓ₁ ℓ h hℓ⟩
  refine ⟨sInf {ℓ : ℝ | TreeBezoutAt 2 ℓ L}, fun ℓ => ⟨fun h => csInf_le hbdd h, fun h => ?_⟩⟩
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨ℓ', hℓ', hlt'⟩ := exists_lt_of_csInf_lt hne hlt
    exact treeBezoutAt_two_mono hL hlt'.le hℓ'
  · -- the infimum is attained: the functional is affine in the length
    rw [treeBezoutAt_two_iff hL]
    intro g hg hgc hlen
    by_contra hcon
    have hneg := not_le.mp hcon
    obtain ⟨x₀, hx₀⟩ := hlen
    have hE0 := treeGenerator_two_nonneg hg.continuous hgc hx₀ hL
    rcases hE0.lt_or_eq with hEpos | hEz
    · -- a length slightly above the infimum is in the set and still gives a negative value
      obtain ⟨ℓ', hℓ', hlt'⟩ := exists_lt_of_csInf_lt hne
        (show sInf {ℓ : ℝ | TreeBezoutAt 2 ℓ L} < ℓ +
          -(zeroSum g + (ℓ - Real.log 2) * treeGenerator 2 g) / treeGenerator 2 g by
          rw [heq]
          linarith [div_pos (neg_pos.mpr hneg) hEpos])
      have h0 := (treeBezoutAt_two_iff hL ℓ').mp hℓ' g hg hgc ⟨x₀, hx₀⟩
      have h2 : ℓ' - ℓ < -(zeroSum g + (ℓ - Real.log 2) * treeGenerator 2 g) /
          treeGenerator 2 g := by linarith
      have h3 := mul_lt_mul_of_pos_right h2 hEpos
      rw [div_mul_cancel₀ _ hEpos.ne'] at h3
      have e : (ℓ' - Real.log 2) * treeGenerator 2 g =
          (ℓ - Real.log 2) * treeGenerator 2 g + (ℓ' - ℓ) * treeGenerator 2 g := by ring
      linarith
    · obtain ⟨ℓ', hℓ'⟩ := hne
      have h0 := (treeBezoutAt_two_iff hL ℓ').mp hℓ' g hg hgc ⟨x₀, hx₀⟩
      rw [← hEz, mul_zero] at h0 hneg
      linarith

/-! ### Odd primes: the generator is indefinite -/

/-- **For an odd prime the generator is negative on a pair of bumps at the distance `log p`.** -/
theorem exists_packet_treeGenerator_neg {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {L : ℝ}
    (hL : Real.log p < L) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∃ x₀ L' : ℝ, L' ≤ L ∧ L' ≤ 2 * Real.log p ∧ ∀ u, u ≤ x₀ ∨ x₀ + L' ≤ u → g u = 0) ∧
      treeGenerator p g < 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  -- half-width of the bumps
  obtain ⟨r, hr, hr1, hr2⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r ≤ L - Real.log p ∧ 4 * r ≤ Real.log p :=
    ⟨min ((L - Real.log p) / 2) (Real.log p / 4), lt_min (by linarith) (by positivity),
      by linarith [min_le_left ((L - Real.log p) / 2) (Real.log p / 4)],
      by linarith [min_le_right ((L - Real.log p) / 2) (Real.log p / 4)]⟩
  have hδ : 0 < r / 2 := by positivity
  have hh : 0 ≤ Real.log p / 2 := by positivity
  have hvan : ∀ u, Real.log p / 2 + r ≤ |u| →
      SelectiveArithmetic.twoBump 1 (Real.log p / 2) r u = 0 := fun u hu =>
    SelectiveArithmetic.twoBump_eq_zero hr hh le_rfl hu
  have hg : ContDiff ℝ 2 (SelectiveArithmetic.twoBump 1 (Real.log p / 2) r) :=
    (SelectiveArithmetic.contDiff_twoBump _ _ _).of_le (by norm_num)
  have hgc : HasCompactSupport (SelectiveArithmetic.twoBump 1 (Real.log p / 2) r) :=
    HasCompactSupport.intro
      (isCompact_Icc (a := -(Real.log p / 2 + r)) (b := Real.log p / 2 + r)) fun u hu =>
      hvan u (by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
        rcases hu with h | h
        · exact le_abs.mpr (Or.inr (by linarith))
        · exact le_abs.mpr (Or.inl (by linarith)))
  refine ⟨_, hg, hgc, ⟨-(Real.log p / 2 + r), Real.log p + 2 * r, by linarith, by linarith,
    fun u hu => hvan u (by
      rcases hu with h | h
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl (by linarith)))⟩, ?_⟩
  -- the autocorrelation at `log p` is the mass of one bump
  have hA := SelectiveArithmetic.packetAutocorr_twoBump 1 (Real.log p / 2) hr (Real.log p)
  have e1 : Real.log p - 2 * (Real.log p / 2) = 0 := by ring
  have e2 : Real.log p + 2 * (Real.log p / 2) = 2 * Real.log p := by ring
  rw [e1, e2, SelectiveArithmetic.packetAutocorr_cutoff_eq_zero hδ (z := Real.log p)
      (by rw [abs_of_pos hlogp]; linarith),
    SelectiveArithmetic.packetAutocorr_cutoff_eq_zero hδ (z := 2 * Real.log p)
      (by rw [abs_of_pos (by positivity)]; linarith)] at hA
  have hM := SelectiveArithmetic.integral_twoBump_sq (s := 1) (h := Real.log p / 2) (by norm_num)
    hr (by linarith)
  have hΦ := SelectiveArithmetic.le_packetAutocorr_cutoff_zero hr
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlt : Real.sqrt p < (p : ℝ) - 1 := by
    rw [Real.sqrt_lt' hpm]
    nlinarith
  have hinv : 1 / ((p : ℝ) - 1) < 1 / Real.sqrt p := one_div_lt_one_div_of_lt hs hlt
  unfold treeGenerator
  rw [hM, hA]
  have e : 2 * packetAutocorr (SelectiveArithmetic.cutoff r (r / 2)) 0 / ((p : ℝ) - 1) -
      2 / Real.sqrt p * ((1 + 1 * 1) * 0 +
        1 * (packetAutocorr (SelectiveArithmetic.cutoff r (r / 2)) 0 + 0)) =
      2 * packetAutocorr (SelectiveArithmetic.cutoff r (r / 2)) 0 *
        (1 / ((p : ℝ) - 1) - 1 / Real.sqrt p) := by ring
  rw [e]
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- **For an odd prime every long tree fails** on packets of any length above `log p`. -/
theorem exists_not_treeBezoutAt_of_three_le {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {L : ℝ}
    (hL : Real.log p < L) : ∃ ℓ₁ : ℝ, ∀ ℓ, ℓ₁ ≤ ℓ → ¬ TreeBezoutAt p ℓ L := by
  obtain ⟨g, hg, hgc, ⟨x₀, L', hL'L, hL'p, hx₀⟩, hneg⟩ :=
    exists_packet_treeGenerator_neg hp hp3 hL
  refine ⟨Real.log p + (|zeroSum g| + 1) / -treeGenerator p g, fun ℓ hℓ h => ?_⟩
  have hlen : ∃ x₁ : ℝ, ∀ u, u ≤ x₁ ∨ x₁ + L ≤ u → g u = 0 :=
    ⟨x₀, fun u hu => hx₀ u (by
      rcases hu with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by linarith))⟩
  have h0 := h g hg hgc hlen
  rw [pairForm_treeDeviation_eq hp _ hg hgc hx₀ hL'p] at h0
  have hE : 0 < -treeGenerator p g := by linarith
  have ht : (|zeroSum g| + 1) / -treeGenerator p g ≤ ℓ - Real.log p := by linarith
  have h1 := mul_le_mul_of_nonneg_right ht hE.le
  rw [div_mul_cancel₀ _ hE.ne'] at h1
  nlinarith [le_abs_self (zeroSum g)]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
