import GaloisForLFunctions.RHTower.MobiusTwoJetCofactorPacket
import GaloisForLFunctions.RHTower.MobiusAbelPrefixGramIntegral

/-!
# Balanced prime–semiprime packets of the cubic Möbius source

For every large `R` there are disjoint sets `A ⊆ {2r : R < r < 2R, r odd prime}` and
`B ⊆ {p : 2R < p < 4R, p prime}` with `|A| = |B| ≥ c R/log R` such that the literal Möbius
subpacket `P_R = Σ_{n ∈ A ∪ B} μ(n) f_n = Σ_A f_a - Σ_B f_b` (`μ(2r) = +1`, `μ(p) = -1`) obeys,
uniformly in `0 ≤ δ ≤ 1`,

`‖P_R‖_δ ≤ C (R^{-(1+δ)/2} + R^{-2/25-δ/2} / log R)`.

This is the cofactor packet at `q = 1`.  At `R = 2^j` the packets live in disjoint dyadic shells
`(2^{j+1}, 2^{j+2})`, their norms have a summable majorant uniform in `δ`, and removing all completed
packets from the finite cubic source `S_N` along `N_J = 2^{J+2}` is a bounded perturbation: the
source is bounded along these cutoffs if and only if the residual literal subsource is.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-! ### Literal Möbius values -/

/-- `μ(2qr) = μ(q)` for odd `q` and a prime `r > max(q, 2)`. -/
theorem moebius_two_mul_mul_prime {q r : ℕ} (hq : Odd q) (hr : r.Prime) (hrq : q < r)
    (hr2 : 2 < r) : μ (2 * q * r) = μ q := by
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  have hcop1 : Nat.Coprime 2 (q * r) := Nat.coprime_two_left.mpr (hq.mul hrodd)
  have hq0 : 0 < q := hq.pos
  have hcop2 : Nat.Coprime q r := by
    have : Nat.Coprime r q := (hr.coprime_iff_not_dvd).mpr fun h => by
      have := Nat.le_of_dvd hq0 h; omega
    exact this.symm
  rw [mul_assoc, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop1,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop2,
    ArithmeticFunction.moebius_apply_prime hr, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

/-- `μ(qp) = -μ(q)` for a prime `p > q ≥ 1`. -/
theorem moebius_mul_prime_of_lt {q p : ℕ} (hq : 1 ≤ q) (hp : p.Prime) (hpq : q < p) :
    μ (q * p) = -μ q := by
  have hcop : Nat.Coprime q p := by
    have : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr fun h => by
      have := Nat.le_of_dvd hq h; omega
    exact this.symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- A finite atom sum with positive nodes has finite Gamma energy. -/
theorem gammaFinite_atomSum {δ : ℝ} (hδ : 0 < 5 + δ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) : GammaFinite δ (fun t => ∑ n ∈ s, c n * atom n t) :=
  GammaFinite.sum s fun n hn =>
    (gammaFinite_atom hδ (by exact_mod_cast (hs n hn : 1 ≤ n))).smul (c n)

/-! ### The prime–semiprime packet (1) -/

/-- **Balanced prime–semiprime two-jet packet (1).** -/
theorem exists_balanced_prime_semiprime_packet :
    ∃ c C R₀ : ℝ, 0 < c ∧ 0 < C ∧ 5 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ A B : Finset ℕ,
        (∀ a ∈ A, ∃ r : ℕ, r.Prime ∧ Odd r ∧ R < r ∧ (r : ℝ) < 2 * R ∧ a = 2 * r) ∧
        (∀ b ∈ B, b.Prime ∧ 2 * R < b ∧ (b : ℝ) < 4 * R) ∧
        Disjoint A B ∧ A.card = B.card ∧ c * R / Real.log R ≤ A.card ∧
        (∀ a ∈ A, μ a = 1) ∧ (∀ b ∈ B, μ b = -1) ∧
        (∀ t : ℝ, ∑ n ∈ A ∪ B, ((μ n : ℤ) : ℝ) * atom n t =
          ∑ a ∈ A, atom a t - ∑ b ∈ B, atom b t) ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ A ∪ B, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (R ^ (-(1 + δ) / 2) + R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R) := by
  obtain ⟨R₀, C, c, hR₀, hC, hc, hpk⟩ := exists_cofactor_two_jet_packet
  refine ⟨c, C, R₀, hc, hC, hR₀, fun R hR => ?_⟩
  have hR5 : 5 ≤ R := hR₀.trans hR
  obtain ⟨Rs, Ps, hRs, hPs, hcard, hcount, hnorm⟩ := hpk R hR 1 le_rfl (by simp; linarith)
  have hRs' : ∀ r ∈ Rs, r.Prime ∧ R < r ∧ (r : ℝ) < 2 * R := fun r hr => by
    have h := hRs r hr
    simp only [one_mul] at h
    exact h
  have hPs' : ∀ p ∈ Ps, p.Prime ∧ 2 * R < p ∧ (p : ℝ) < 4 * R := fun p hp => by
    have h := hPs p hp
    simp only [one_mul] at h
    exact h
  have hr2 : ∀ r ∈ Rs, 2 < r := fun r hr => by
    have h := (hRs' r hr).2.1
    have : (2 : ℝ) < r := by linarith
    exact_mod_cast this
  have hp2 : ∀ p ∈ Ps, 2 < p := fun p hp => by
    have h := (hPs' p hp).2.1
    have : (2 : ℝ) < p := by linarith
    exact_mod_cast this
  have hinj : Function.Injective (fun r : ℕ => 2 * r) := fun a b h => by simpa using h
  have hdisj : Disjoint (Rs.image (fun r : ℕ => 2 * r)) Ps := by
    rw [Finset.disjoint_left]
    intro x hx hxP
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hx
    have hodd : Odd (2 * r) := ((hPs' _ hxP).1).odd_of_ne_two (by have := hr2 r hr; omega)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul r)
  have hμA : ∀ a ∈ Rs.image (fun r : ℕ => 2 * r), μ a = 1 := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    have h := moebius_two_mul_mul_prime odd_one (hRs' r hr).1 (by have := hr2 r hr; omega)
      (hr2 r hr)
    rw [mul_one] at h
    rw [h, ArithmeticFunction.moebius_apply_one]
  have hμB : ∀ b ∈ Ps, μ b = -1 := fun b hb =>
    ArithmeticFunction.moebius_apply_prime (hPs' b hb).1
  have hsum : ∀ t : ℝ, ∑ n ∈ Rs.image (fun r : ℕ => 2 * r) ∪ Ps, ((μ n : ℤ) : ℝ) * atom n t =
      ∑ a ∈ Rs.image (fun r : ℕ => 2 * r), atom a t - ∑ b ∈ Ps, atom b t := by
    intro t
    rw [sum_union hdisj]
    have h1 : ∑ n ∈ Rs.image (fun r : ℕ => 2 * r), ((μ n : ℤ) : ℝ) * atom n t =
        ∑ a ∈ Rs.image (fun r : ℕ => 2 * r), atom a t :=
      sum_congr rfl fun n hn => by rw [hμA n hn]; simp
    have h2 : ∑ n ∈ Ps, ((μ n : ℤ) : ℝ) * atom n t = -∑ b ∈ Ps, atom b t := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun n hn => by rw [hμB n hn]; simp
    rw [h1, h2]
    ring
  refine ⟨Rs.image (fun r : ℕ => 2 * r), Ps, fun a ha => ?_, hPs', hdisj, ?_, ?_, hμA, hμB, hsum,
    fun δ hδ0 hδ1 => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    exact ⟨r, (hRs' r hr).1, (hRs' r hr).1.odd_of_ne_two (by have := hr2 r hr; omega),
      (hRs' r hr).2.1, (hRs' r hr).2.2, rfl⟩
  · rw [card_image_of_injective _ hinj, hcard]
  · rw [card_image_of_injective _ hinj]
    have := hcount
    simp only [Nat.cast_one, one_mul] at this
    exact this
  · have hfun : (fun t => ∑ n ∈ Rs.image (fun r : ℕ => 2 * r) ∪ Ps, ((μ n : ℤ) : ℝ) * atom n t) =
        fun t => ∑ r ∈ Rs, atom ((2 * 1 * r : ℕ) : ℝ) t - ∑ p ∈ Ps, atom ((1 * p : ℕ) : ℝ) t := by
      funext t
      rw [hsum t, sum_image (fun a _ b _ h => hinj h)]
      simp
    rw [hfun]
    have h := hnorm δ hδ0 hδ1
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact h

/-! ### Dyadic shells and the cofinal reduction -/

/-- Packets supported in disjoint dyadic shells with summable norms: removing the completed
ones from `S_{2^{J+2}}` leaves a literal subsource at bounded distance. -/
theorem cofinal_packet_reduction (U : ℕ → Finset ℕ) (b : ℕ → ℝ) (hb : Summable b)
    (hsupp : ∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2))
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hnorm : ∀ j, gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j) :
    (∀ J : ℕ, ∀ t : ℝ, mobiusCubicSource (2 ^ (J + 2)) t -
        ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t =
      ∑ n ∈ Icc 1 (2 ^ (J + 2)) \ (range (J + 1)).biUnion U, ((μ n : ℤ) : ℝ) * atom n t) ∧
    ((∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (mobiusCubicSource (2 ^ (J + 2))) ≤ B) ↔
      ∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
        ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ B) := by
  have hδ : 0 < 5 + δ := by linarith
  have hb0 : ∀ j, 0 ≤ b j := fun j => (gammaNorm_nonneg _ _).trans (hnorm j)
  -- the shells are disjoint
  have hdisj : ∀ J : ℕ, (↑(range (J + 1)) : Set ℕ).PairwiseDisjoint U := by
    intro J j _ j' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    have h1 := hsupp j n hn
    have h2 := hsupp j' n hn'
    rcases lt_or_gt_of_ne hne with h | h
    · have : 2 ^ (j + 2) ≤ 2 ^ (j' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : 2 ^ (j' + 2) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hsub : ∀ J : ℕ, (range (J + 1)).biUnion U ⊆ Icc 1 (2 ^ (J + 2)) := by
    intro J n hn
    obtain ⟨j, hj, hnj⟩ := mem_biUnion.mp hn
    have h := hsupp j n hnj
    have hjJ := mem_range.mp hj
    have : 2 ^ (j + 2) ≤ 2 ^ (J + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hid : ∀ J : ℕ, ∀ t : ℝ, mobiusCubicSource (2 ^ (J + 2)) t -
      ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t =
    ∑ n ∈ Icc 1 (2 ^ (J + 2)) \ (range (J + 1)).biUnion U, ((μ n : ℤ) : ℝ) * atom n t := by
    intro J t
    unfold mobiusCubicSource
    rw [← sum_biUnion (hdisj J), ← sum_sdiff (hsub J)]
    ring
  refine ⟨hid, ?_⟩
  -- the packets have total norm at most `Σ' b`
  have hU1 : ∀ j, ∀ n ∈ U j, 1 ≤ n := fun j n hn => by
    have := (hsupp j n hn).1
    have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    omega
  have hfinU : ∀ j, GammaFinite δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) :=
    fun j => gammaFinite_atomSum hδ (U j) _ (hU1 j)
  have hfinS : ∀ N : ℕ, GammaFinite δ (mobiusCubicSource N) := fun N =>
    gammaFinite_atomSum hδ (Icc 1 N) _ (fun n hn => (mem_Icc.mp hn).1)
  have hP : ∀ J : ℕ, gammaNorm δ (fun t => ∑ j ∈ range (J + 1),
      ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ ∑' j, b j := by
    intro J
    refine (gammaNorm_sum_le hδ _ fun j _ => hfinU j).trans ?_
    refine (sum_le_sum fun j _ => hnorm j).trans ?_
    exact hb.sum_le_tsum _ fun j _ => hb0 j
  have hdiff : ∀ J : ℕ, |gammaNorm δ (mobiusCubicSource (2 ^ (J + 2))) -
      gammaNorm δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
        ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t)| ≤ ∑' j, b j := by
    intro J
    have hG : GammaFinite δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
        ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) :=
      (hfinS _).sub (GammaFinite.sum _ fun j _ => hfinU j)
    refine (abs_gammaNorm_sub_le hδ (hfinS _) hG).trans ?_
    have e : (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
        (mobiusCubicSource (2 ^ (J + 2)) t -
          ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t)) =
        fun t => ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t := by
      funext t; ring
    rw [e]
    exact hP J
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + ∑' j, b j, fun J => ?_⟩
    have := abs_le.mp (hdiff J)
    linarith [hB J]
  · rintro ⟨B, hB⟩
    refine ⟨B + ∑' j, b j, fun J => ?_⟩
    have := abs_le.mp (hdiff J)
    linarith [hB J]

/-- `(2^j)^{-x} = (2^{-x})^j`. -/
theorem two_pow_rpow_neg (j : ℕ) (x : ℝ) :
    ((2 : ℝ) ^ j) ^ (-x) = ((2 : ℝ) ^ (-x)) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- **Dyadic packets (2).**  The packets at `R = 2^j` occupy disjoint shells and
`Σ_j sup_{0≤δ≤1} ‖P_{2^j}‖_δ < ∞`; hence removing them is a bounded perturbation along
`N_J = 2^{J+2}`. -/
theorem exists_dyadic_prime_semiprime_packets :
    ∃ c : ℝ, 0 < c ∧ ∃ A B : ℕ → Finset ℕ, ∃ b : ℕ → ℝ, Summable b ∧
      (∀ j, ∀ a ∈ A j, ∃ r : ℕ, r.Prime ∧ Odd r ∧ a = 2 * r) ∧ (∀ j, ∀ p ∈ B j, p.Prime) ∧
      (∀ j, Disjoint (A j) (B j)) ∧ (∀ j, (A j).card = (B j).card) ∧
      (∀ᶠ j in atTop, c * 2 ^ j / Real.log (2 ^ j) ≤ (A j).card) ∧
      (∀ j, ∀ a ∈ A j, μ a = 1) ∧ (∀ j, ∀ p ∈ B j, μ p = -1) ∧
      (∀ j, ∀ n ∈ A j ∪ B j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2)) ∧
      ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ A j ∪ B j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j := by
  obtain ⟨c, C, R₀, hc, hC, hR₀, hpk⟩ := exists_balanced_prime_semiprime_packet
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, R₀ ≤ (2 : ℝ) ^ j₀ :=
    pow_unbounded_of_one_lt R₀ (by norm_num) |>.imp fun _ h => h.le
  have hex : ∀ j : ℕ, ∃ AB : Finset ℕ × Finset ℕ,
      (j₀ ≤ j → (∀ a ∈ AB.1, ∃ r : ℕ, r.Prime ∧ Odd r ∧ (2 : ℝ) ^ j < r ∧
          (r : ℝ) < 2 * 2 ^ j ∧ a = 2 * r) ∧
        (∀ b ∈ AB.2, b.Prime ∧ 2 * (2 : ℝ) ^ j < b ∧ (b : ℝ) < 4 * 2 ^ j) ∧
        Disjoint AB.1 AB.2 ∧ AB.1.card = AB.2.card ∧
        c * 2 ^ j / Real.log (2 ^ j) ≤ AB.1.card ∧
        (∀ a ∈ AB.1, μ a = 1) ∧ (∀ b ∈ AB.2, μ b = -1) ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ AB.1 ∪ AB.2, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (((2 : ℝ) ^ j) ^ (-(1 + δ) / 2) +
              ((2 : ℝ) ^ j) ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log (2 ^ j))) ∧
      (j < j₀ → AB = (∅, ∅)) := by
    intro j
    by_cases hj : j₀ ≤ j
    · have hR : R₀ ≤ (2 : ℝ) ^ j :=
        hj₀.trans (pow_le_pow_right₀ (by norm_num) hj)
      obtain ⟨A, B, hA, hB, hd, hcard, hcount, hμA, hμB, _, hn⟩ := hpk _ hR
      exact ⟨(A, B), fun _ => ⟨hA, hB, hd, hcard, hcount, hμA, hμB, hn⟩, fun h => absurd hj (by omega)⟩
    · exact ⟨(∅, ∅), fun h => absurd h hj, fun _ => rfl⟩
  choose AB hAB hAB0 using hex
  set b : ℕ → ℝ := fun j => C * (((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ j +
    ((2 : ℝ) ^ (-(2 / 25 : ℝ))) ^ j / Real.log 2) with hbdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Summable b := by
    have h1 : Summable (fun j : ℕ => ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ j) :=
      summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    have h2 : Summable (fun j : ℕ => ((2 : ℝ) ^ (-(2 / 25 : ℝ))) ^ j) :=
      summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    exact (h1.add (h2.div_const _)).mul_left C
  refine ⟨c, hc, fun j => (AB j).1, fun j => (AB j).2, b, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j a ha
    by_cases hj : j₀ ≤ j
    · obtain ⟨r, hr, hodd, -, -, rfl⟩ := (hAB j hj).1 a ha
      exact ⟨r, hr, hodd, rfl⟩
    · simp [hAB0 j (by omega)] at ha
  · intro j p hp
    by_cases hj : j₀ ≤ j
    · exact ((hAB j hj).2.1 p hp).1
    · simp [hAB0 j (by omega)] at hp
  · intro j
    by_cases hj : j₀ ≤ j
    · exact (hAB j hj).2.2.1
    · simp [hAB0 j (by omega)]
  · intro j
    by_cases hj : j₀ ≤ j
    · exact (hAB j hj).2.2.2.1
    · simp [hAB0 j (by omega)]
  · filter_upwards [eventually_ge_atTop j₀] with j hj
    exact (hAB j hj).2.2.2.2.1
  · intro j a ha
    by_cases hj : j₀ ≤ j
    · exact (hAB j hj).2.2.2.2.2.1 a ha
    · simp [hAB0 j (by omega)] at ha
  · intro j p hp
    by_cases hj : j₀ ≤ j
    · exact (hAB j hj).2.2.2.2.2.2.1 p hp
    · simp [hAB0 j (by omega)] at hp
  · intro j n hn
    by_cases hj : j₀ ≤ j
    · have hjj := hAB j hj
      rcases mem_union.mp hn with hn | hn
      · obtain ⟨r, -, -, h1, h2, rfl⟩ := hjj.1 n hn
        have e1 : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
        have e2 : ((2 ^ (j + 2) : ℕ) : ℝ) = 4 * (2 : ℝ) ^ j := by push_cast; ring
        constructor
        · have : ((2 ^ (j + 1) : ℕ) : ℝ) < ((2 * r : ℕ) : ℝ) := by rw [e1]; push_cast; linarith
          exact_mod_cast this
        · have : ((2 * r : ℕ) : ℝ) < ((2 ^ (j + 2) : ℕ) : ℝ) := by rw [e2]; push_cast; linarith
          exact_mod_cast this
      · obtain ⟨-, h1, h2⟩ := hjj.2.1 n hn
        have e1 : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
        have e2 : ((2 ^ (j + 2) : ℕ) : ℝ) = 4 * (2 : ℝ) ^ j := by push_cast; ring
        constructor
        · have : ((2 ^ (j + 1) : ℕ) : ℝ) < (n : ℝ) := by rw [e1]; linarith
          exact_mod_cast this
        · have : (n : ℝ) < ((2 ^ (j + 2) : ℕ) : ℝ) := by rw [e2]; linarith
          exact_mod_cast this
    · simp [hAB0 j (by omega)] at hn
  · intro j δ hδ0 hδ1
    by_cases hj : j₀ ≤ j
    · refine ((hAB j hj).2.2.2.2.2.2.2 δ hδ0 hδ1).trans ?_
      have hj1 : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        subst hj0
        have : R₀ ≤ 1 := by simpa using hj₀.trans (pow_le_pow_right₀ (by norm_num) hj)
        linarith
      have hlogj : Real.log 2 ≤ Real.log (2 ^ j) := by
        rw [Real.log_pow]
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        nlinarith
      have hp1 : ((2 : ℝ) ^ j) ^ (-(1 + δ) / 2) ≤ ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ j := by
        rw [← two_pow_rpow_neg]
        apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
      have hp2 : ((2 : ℝ) ^ j) ^ (-(2 / 25 : ℝ) - δ / 2) ≤ ((2 : ℝ) ^ (-(2 / 25 : ℝ))) ^ j := by
        rw [← two_pow_rpow_neg]
        apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
      have hq0 : 0 ≤ ((2 : ℝ) ^ j) ^ (-(2 / 25 : ℝ) - δ / 2) := Real.rpow_nonneg (by positivity) _
      have hdiv : ((2 : ℝ) ^ j) ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log (2 ^ j) ≤
          ((2 : ℝ) ^ (-(2 / 25 : ℝ))) ^ j / Real.log 2 := by
        calc ((2 : ℝ) ^ j) ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log (2 ^ j)
            ≤ ((2 : ℝ) ^ j) ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log 2 :=
              div_le_div_of_nonneg_left hq0 hlog2 hlogj
          _ ≤ _ := by gcongr
      simp only [hbdef]
      gcongr
    · simp only [hAB0 j (by omega), Finset.union_empty, Finset.sum_empty]
      have : gammaNorm δ (fun _ : ℝ => (0 : ℝ)) = 0 := by
        simp [gammaNorm, gammaEnergy, gammaInner]
      rw [this]
      simp only [hbdef]
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(1 / 2 : ℝ))
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(2 / 25 : ℝ))
      positivity

end RHTower.CubicGamma
