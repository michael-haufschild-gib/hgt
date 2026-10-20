import GaloisForLFunctions.TransHorizonIncidenceMechanics.ReceiverRowParsevalSpectrumAndHorizonUniformVariance
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy
import GaloisForLFunctions.RHTower.Sieve.SquarefreeWindowCount
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDensityBound

/-!
# The parity twin of the damped Möbius weight

The damped Möbius weight `c_ε(d) = μ(d) d^{-ε}` has Ramanujan coefficients
`w_ε(e) = Σ_k c_ε(ek)/(ek) = ρ_ε μ(e)/D_ε(e)`, `D_ε(e) = ∏_{p | e} (p^{1+ε} - 1)`. Every
translation statistic of its divisor-sum signal (mean, variance, lag covariances, successor energy,
primitive energy) is diagonal in these coordinates and sees only `w_ε(e)²`; the sign `μ(e)` is the
parity of the number of prime factors of the modulus.

The **parity twin** is the weight whose Ramanujan coefficients are `μ(e) w_ε(e) = |w_ε(e)|`. It is
the explicit nonnegative squarefree weight

`c'_ε(d) = (ρ_ε/U_ε) · d · μ²(d) ∏_{p | d} 1/(p^{1+ε} - 2)`,   `U_ε = Σ_k μ²(k) ∏_{p | k} 1/(p^{1+ε} - 2)`.

The identity `Σ_k c'_ε(ek)/(ek) = μ(e) w_ε(e)` rests on the coprime recursion
`U_e = (1 + u_ε(p)) U_{pe}` for the restricted masses `U_e = Σ_{(k,e)=1} μ²(k) u_ε(k)`, read along the
prime dilation `k ↦ pk`, and on `u/(1+u) = 1/(p^{1+ε} - 1)`. The twin dominates the Liouville row:
`c'_ε(d) ≥ (ρ_ε/U_ε) μ²(d) d^{-ε}`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The local factor and the squarefree shape -/

/-- Local factor `u_ε(p) = 1/(p^{1+ε} - 2)` of the parity twin. -/
def parityTwinLocal (ε : ℝ) (p : ℕ) : ℝ := 1 / ((p : ℝ) ^ (1 + ε) - 2)

/-- `p^{1+ε} > 2` at every prime. -/
theorem two_lt_prime_rpow {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    (2 : ℝ) < (p : ℝ) ^ (1 + ε) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
    _ < 2 ^ (1 + ε) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    _ ≤ (p : ℝ) ^ (1 + ε) := Real.rpow_le_rpow (by norm_num) hp2 (by linarith)

theorem parityTwinLocal_pos {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    0 < parityTwinLocal ε p :=
  one_div_pos.mpr (sub_pos.mpr (two_lt_prime_rpow hε hp))

/-- `u/(1+u) = 1/(p^{1+ε} - 1)`: the twin's local factor against the Ramanujan denominator. -/
theorem parityTwinLocal_div_one_add {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    parityTwinLocal ε p / (1 + parityTwinLocal ε p) = 1 / ((p : ℝ) ^ (1 + ε) - 1) := by
  have h2 := two_lt_prime_rpow hε hp
  unfold parityTwinLocal
  set P := (p : ℝ) ^ (1 + ε)
  have ha : P - 2 ≠ 0 := by linarith
  have hb : P - 1 ≠ 0 := by linarith
  have hc : 1 + 1 / (P - 2) = (P - 1) / (P - 2) := by field_simp; ring
  rw [hc, div_div_div_cancel_right₀ ha, one_div]

/-- `p · u_ε(p) ≥ p^{-ε}`. -/
theorem rpow_neg_le_mul_parityTwinLocal {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (-ε) ≤ (p : ℝ) * parityTwinLocal ε p := by
  have h2 := two_lt_prime_rpow hε hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq : (p : ℝ) ^ (1 + ε) = p * (p : ℝ) ^ ε := by
    rw [Real.rpow_add hp0, Real.rpow_one]
  rw [Real.rpow_neg hp0.le, parityTwinLocal, mul_one_div,
    div_eq_mul_inv, ← one_div, ← div_eq_mul_inv]
  have hpe : 0 < (p : ℝ) ^ ε := Real.rpow_pos_of_pos hp0 ε
  rw [div_le_div_iff₀ hpe (by linarith)]
  nlinarith

/-- The squarefree shape `μ²(d) ∏_{p | d} u_ε(p)`. -/
def parityTwinShape (ε : ℝ) (d : ℕ) : ℝ :=
  if Squarefree d then ∏ p ∈ d.primeFactors, parityTwinLocal ε p else 0

@[simp] theorem parityTwinShape_zero (ε : ℝ) : parityTwinShape ε 0 = 0 := by
  simp [parityTwinShape]

@[simp] theorem parityTwinShape_one (ε : ℝ) : parityTwinShape ε 1 = 1 := by
  simp [parityTwinShape]

theorem parityTwinShape_nonneg {ε : ℝ} (hε : 0 < ε) (d : ℕ) : 0 ≤ parityTwinShape ε d := by
  unfold parityTwinShape
  split_ifs
  · exact prod_nonneg fun p hp => (parityTwinLocal_pos hε (Nat.prime_of_mem_primeFactors hp)).le
  · exact le_rfl

/-- Multiplicativity of the shape on coprime pairs, and vanishing otherwise. -/
theorem parityTwinShape_mul (ε : ℝ) (e k : ℕ) :
    parityTwinShape ε (e * k) =
      if Nat.Coprime e k then parityTwinShape ε e * parityTwinShape ε k else 0 := by
  unfold parityTwinShape
  by_cases hsq : Squarefree (e * k)
  · obtain ⟨hco, hse, hsk⟩ := Nat.squarefree_mul_iff.mp hsq
    have he : e ≠ 0 := fun h => not_squarefree_zero (h ▸ hse)
    have hk : k ≠ 0 := fun h => not_squarefree_zero (h ▸ hsk)
    rw [if_pos hsq, if_pos hco, if_pos hse, if_pos hsk, Nat.primeFactors_mul he hk,
      prod_union (Nat.Coprime.disjoint_primeFactors hco)]
  · rw [if_neg hsq]
    split_ifs with hco hse hsk <;> try simp
    exact (hsq (Nat.squarefree_mul_iff.mpr ⟨hco, hse, hsk⟩)).elim

/-- `d · shape(d) ≥ μ²(d) d^{-ε}`. -/
theorem rpow_neg_le_mul_parityTwinShape {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : Squarefree d) :
    (d : ℝ) ^ (-ε) ≤ (d : ℝ) * parityTwinShape ε d := by
  rw [parityTwinShape, if_pos hd]
  have hd' : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [hd', ← Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← prod_mul_distrib]
  exact prod_le_prod (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    fun p hp => rpow_neg_le_mul_parityTwinLocal hε (Nat.prime_of_mem_primeFactors hp)

/-! ### Summability of the shape -/

/-- The local ratio `u_ε(p) p^{1+ε/2}` is at most one once `p^{ε/2} ≥ 3`. -/
private theorem parityTwinLocal_mul_le_one {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime)
    (h3 : (3 : ℝ) ≤ (p : ℝ) ^ (ε / 2)) :
    parityTwinLocal ε p * (p : ℝ) ^ (1 + ε / 2) ≤ 1 := by
  have h2 := two_lt_prime_rpow hε hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsplit : (p : ℝ) ^ (1 + ε) = (p : ℝ) ^ (1 + ε / 2) * (p : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hp0]; ring_nf
  have hpos : (1 : ℝ) ≤ (p : ℝ) ^ (1 + ε / 2) :=
    Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) (by linarith)
  rw [parityTwinLocal, one_div_mul_eq_div, div_le_one (by linarith)]
  nlinarith

/-- The shape is dominated by `C d^{-1-ε/2}` with a constant collecting the small primes. -/
theorem exists_parityTwinShape_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d →
      parityTwinShape ε d ≤ C * (d : ℝ) ^ (-1 - ε / 2) := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → (3 : ℝ) ≤ (p : ℝ) ^ (ε / 2) := by
    have ht : Tendsto (fun x : ℝ => x ^ (ε / 2)) atTop atTop := tendsto_rpow_atTop (by linarith)
    obtain ⟨X, hX⟩ := (ht.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3 |>.exists_forall_of_atTop
    exact ⟨X, fun p hp => hX p hp⟩
  set r : ℕ → ℝ := fun p => max 1 (parityTwinLocal ε p * (p : ℝ) ^ (1 + ε / 2))
  set C : ℝ := ∏ p ∈ (range P).filter Nat.Prime, r p
  have hr1 : ∀ p, 1 ≤ r p := fun p => le_max_left _ _
  refine ⟨C, prod_pos fun p _ => lt_of_lt_of_le one_pos (hr1 p), fun d hd => ?_⟩
  unfold parityTwinShape
  split_ifs with hsq
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hprod : (d : ℝ) ^ (-1 - ε / 2) = ∏ p ∈ d.primeFactors, (p : ℝ) ^ (-1 - ε / 2) := by
      have hd' : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
        rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
      rw [hd', Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    have hloc : ∀ p ∈ d.primeFactors,
        parityTwinLocal ε p ≤ (if p < P then r p else 1) * (p : ℝ) ^ (-1 - ε / 2) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hinv : (p : ℝ) ^ (-1 - ε / 2) * (p : ℝ) ^ (1 + ε / 2) = 1 := by
        rw [← Real.rpow_add hp0]; ring_nf; exact Real.rpow_zero _
      have hpos : 0 < (p : ℝ) ^ (1 + ε / 2) := Real.rpow_pos_of_pos hp0 _
      have key : parityTwinLocal ε p =
          (parityTwinLocal ε p * (p : ℝ) ^ (1 + ε / 2)) * (p : ℝ) ^ (-1 - ε / 2) := by
        rw [mul_assoc, mul_comm ((p : ℝ) ^ (1 + ε / 2)), hinv, mul_one]
      rw [key]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hp0.le _)
      split_ifs with hlt
      · exact le_max_right _ _
      · exact parityTwinLocal_mul_le_one hε hpp (hP p (not_lt.mp hlt))
    calc ∏ p ∈ d.primeFactors, parityTwinLocal ε p
        ≤ ∏ p ∈ d.primeFactors, ((if p < P then r p else 1) * (p : ℝ) ^ (-1 - ε / 2)) :=
          prod_le_prod (fun p hp =>
            (parityTwinLocal_pos hε (Nat.prime_of_mem_primeFactors hp)).le) hloc
      _ = (∏ p ∈ d.primeFactors, (if p < P then r p else 1)) * (d : ℝ) ^ (-1 - ε / 2) := by
          rw [prod_mul_distrib, hprod]
      _ ≤ C * (d : ℝ) ^ (-1 - ε / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd0.le _)
          rw [← prod_filter]
          refine prod_le_prod_of_subset_of_one_le ?_ (fun p _ => (one_pos.trans_le (hr1 p)).le)
            fun p _ _ => hr1 p
          intro p hp
          simp only [mem_filter, Nat.mem_primeFactors] at hp
          simp only [mem_filter, mem_range]
          exact ⟨hp.2, hp.1.1⟩
  · exact mul_nonneg (prod_pos fun p _ => lt_of_lt_of_le one_pos (hr1 p)).le
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)

theorem summable_parityTwinShape {ε : ℝ} (hε : 0 < ε) : Summable (parityTwinShape ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_parityTwinShape_le hε
  refine Summable.of_nonneg_of_le (parityTwinShape_nonneg hε) (fun d => ?_)
    ((Real.summable_nat_rpow.mpr (by linarith : -1 - ε / 2 < -1)).mul_left C)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [parityTwinShape_zero]
    exact mul_nonneg hC0.le (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
  · exact hC d hd

/-! ### Coprime masses and the prime recursion -/

/-- Coprime mass `U_e = Σ_{(k,e)=1} μ²(k) u_ε(k)`. -/
def parityTwinCoprimeMass (ε : ℝ) (e : ℕ) : ℝ :=
  ∑' k : ℕ, if Nat.Coprime k e then parityTwinShape ε k else 0

theorem summable_parityTwinCoprime {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    Summable (fun k : ℕ => if Nat.Coprime k e then parityTwinShape ε k else 0) :=
  (summable_parityTwinShape hε).of_nonneg_of_le
    (fun k => by split_ifs <;> simp [parityTwinShape_nonneg hε])
    (fun k => by split_ifs <;> simp [parityTwinShape_nonneg hε])

/-- **Prime recursion.** For a prime `p ∤ e`: `U_e = (1 + u_ε(p)) U_{pe}`; the multiples of `p`
are the image of the dilation `k ↦ pk`. -/
theorem parityTwinCoprimeMass_prime {ε : ℝ} (hε : 0 < ε) {p e : ℕ} (hp : p.Prime)
    (hpe : ¬ p ∣ e) :
    parityTwinCoprimeMass ε e = (1 + parityTwinLocal ε p) * parityTwinCoprimeMass ε (p * e) := by
  classical
  set f : ℕ → ℝ := fun k => if Nat.Coprime k e then parityTwinShape ε k else 0
  have hf : Summable f := summable_parityTwinCoprime hε e
  have hf0 : ∀ k, 0 ≤ f k := fun k => by
    simp only [f]; split_ifs
    exacts [parityTwinShape_nonneg hε k, le_rfl]
  set g : ℕ → ℝ := fun k => if p ∣ k then 0 else f k
  set h : ℕ → ℝ := fun k => if p ∣ k then f k else 0
  have hg : Summable g := hf.of_nonneg_of_le
    (fun k => by simp only [g]; split_ifs; exacts [le_rfl, hf0 k])
    (fun k => by simp only [g]; split_ifs; exacts [hf0 k, le_rfl])
  have hh : Summable h := hf.of_nonneg_of_le
    (fun k => by simp only [h]; split_ifs; exacts [hf0 k, le_rfl])
    (fun k => by simp only [h]; split_ifs; exacts [le_rfl, hf0 k])
  have hfgh : f = fun k => g k + h k := by
    funext k; simp only [g, h]; split_ifs <;> simp
  have hcop : ∀ k, Nat.Coprime k (p * e) ↔ ¬ p ∣ k ∧ Nat.Coprime k e := fun k => by
    rw [Nat.coprime_mul_iff_right, Nat.coprime_comm, hp.coprime_iff_not_dvd]
  have hgU : ∑' k, g k = parityTwinCoprimeMass ε (p * e) := by
    unfold parityTwinCoprimeMass
    refine tsum_congr fun k => ?_
    simp only [g, f, hcop]
    by_cases hk : p ∣ k <;> simp [hk]
  have hhU : ∑' k, h k = parityTwinLocal ε p * parityTwinCoprimeMass ε (p * e) := by
    have hinj : Function.Injective (fun k : ℕ => p * k) :=
      fun a b hab => Nat.eq_of_mul_eq_mul_left hp.pos hab
    have hsupp : Function.support h ⊆ Set.range (fun k : ℕ => p * k) := by
      intro k hk
      rw [Function.mem_support] at hk
      by_cases hpk : p ∣ k
      · obtain ⟨j, rfl⟩ := hpk; exact ⟨j, rfl⟩
      · exact (hk (by simp [h, hpk])).elim
    rw [← hinj.tsum_eq hsupp, parityTwinCoprimeMass, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hpe' : Nat.Coprime p e := hp.coprime_iff_not_dvd.mpr hpe
    have hpk' : Nat.Coprime (p * k) e ↔ Nat.Coprime k e := by
      rw [Nat.coprime_mul_iff_left]; exact ⟨fun h => h.2, fun h => ⟨hpe', h⟩⟩
    have hs : parityTwinShape ε p = parityTwinLocal ε p := by
      simp [parityTwinShape, hp.squarefree, hp.primeFactors]
    show (if p ∣ p * k then f (p * k) else 0) =
      parityTwinLocal ε p * (if Nat.Coprime k (p * e) then parityTwinShape ε k else 0)
    rw [if_pos (dvd_mul_right p k)]
    show (if Nat.Coprime (p * k) e then parityTwinShape ε (p * k) else 0) = _
    rw [parityTwinShape_mul]
    by_cases hkp : p ∣ k
    · have hnc : ¬ Nat.Coprime p k := (Nat.Prime.dvd_iff_not_coprime hp).mp hkp
      have hnc' : ¬ Nat.Coprime k (p * e) := fun h => ((hcop k).mp h).1 hkp
      rw [if_neg hnc, if_neg hnc']
      split_ifs <;> ring
    · have hc : Nat.Coprime p k := hp.coprime_iff_not_dvd.mpr hkp
      by_cases hke : Nat.Coprime k e
      · have hc' : Nat.Coprime k (p * e) := (hcop k).mpr ⟨hkp, hke⟩
        rw [if_pos (hpk'.mpr hke), if_pos hc, if_pos hc', hs]
      · have hc' : ¬ Nat.Coprime k (p * e) := fun h => hke ((hcop k).mp h).2
        rw [if_neg (fun h => hke (hpk'.mp h)), if_neg hc']
        ring
  calc parityTwinCoprimeMass ε e = ∑' k, f k := rfl
    _ = ∑' k, g k + ∑' k, h k := by rw [hfgh]; exact hg.tsum_add hh
    _ = _ := by rw [hgU, hhU]; ring

theorem parityTwinCoprimeMass_one_eq_tsum (ε : ℝ) :
    parityTwinCoprimeMass ε 1 = ∑' k, parityTwinShape ε k := by
  simp [parityTwinCoprimeMass]

theorem parityTwinCoprimeMass_one_pos {ε : ℝ} (hε : 0 < ε) : 0 < parityTwinCoprimeMass ε 1 := by
  rw [parityTwinCoprimeMass_one_eq_tsum]
  have h := (summable_parityTwinShape hε).le_tsum 1 (fun k _ => parityTwinShape_nonneg hε k)
  rw [parityTwinShape_one] at h
  linarith

/-- **Product formula.** For squarefree `e`: `U_1 = U_e ∏_{p | e} (1 + u_ε(p))`. -/
theorem parityTwinCoprimeMass_one_eq {ε : ℝ} (hε : 0 < ε) {e : ℕ} (he : Squarefree e) :
    parityTwinCoprimeMass ε 1 =
      parityTwinCoprimeMass ε e * ∏ p ∈ e.primeFactors, (1 + parityTwinLocal ε p) := by
  induction e using induction_on_primes with
  | zero => exact (not_squarefree_zero he).elim
  | one => simp
  | prime_mul p a hp ih =>
    have hpa : ¬ p ∣ a := fun hdvd => by
      have := Nat.squarefree_mul_iff.mp he
      exact (Nat.Prime.dvd_iff_not_coprime hp).mp hdvd this.1
    have ha : Squarefree a := (Nat.squarefree_mul_iff.mp he).2.2
    have ha0 : a ≠ 0 := fun h => not_squarefree_zero (h ▸ ha)
    have hnot : p ∉ a.primeFactors := fun h => hpa (Nat.dvd_of_mem_primeFactors h)
    rw [ih ha, parityTwinCoprimeMass_prime hε hp hpa, Nat.primeFactors_mul hp.ne_zero ha0,
      hp.primeFactors, singleton_union, prod_insert hnot]
    ring

theorem parityTwinCoprimeMass_pos {ε : ℝ} (hε : 0 < ε) {e : ℕ} (he : Squarefree e) :
    0 < parityTwinCoprimeMass ε e := by
  have h1 := parityTwinCoprimeMass_one_pos hε
  rw [parityTwinCoprimeMass_one_eq hε he] at h1
  have hP : 0 < ∏ p ∈ e.primeFactors, (1 + parityTwinLocal ε p) :=
    prod_pos fun p hp => by linarith [parityTwinLocal_pos hε (Nat.prime_of_mem_primeFactors hp)]
  exact pos_of_mul_pos_left h1 hP.le

/-! ### The twin weight and its Ramanujan coefficients -/

/-- The damped density `ρ_ε = 1/ζ(1+ε)`, the mean of `τ_ε`. -/
abbrev dampedDensity (ε : ℝ) : ℝ := (RHTower.pmPowerDampedDivisorDensity ε).re

/-- **The parity twin** `c'_ε(d) = (ρ_ε/U_1) · d · μ²(d) ∏_{p | d} u_ε(p)`. -/
def parityTwinWeight (ε : ℝ) (d : ℕ) : ℝ :=
  dampedDensity ε / parityTwinCoprimeMass ε 1 * d * parityTwinShape ε d

/-- The Ramanujan coefficient `W_c(e) = Σ_k c(ek)/(ek)` of a weight. -/
def weightRamanujanCoeff (c : ℕ → ℝ) (e : ℕ) : ℝ := ∑' k : ℕ, c (e * k) / ((e * k : ℕ) : ℝ)

theorem parityTwinWeight_nonneg {ε : ℝ} (hε : 0 < ε) (d : ℕ) : 0 ≤ parityTwinWeight ε d :=
  mul_nonneg (mul_nonneg (div_nonneg (RHTower.pmPowerDampedDivisorDensity_re_pos hε).le
    (parityTwinCoprimeMass_one_pos hε).le) (Nat.cast_nonneg d)) (parityTwinShape_nonneg hε d)

theorem parityTwinWeight_div (ε : ℝ) (n : ℕ) :
    parityTwinWeight ε n / n = dampedDensity ε / parityTwinCoprimeMass ε 1 * parityTwinShape ε n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [parityTwinWeight]
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold parityTwinWeight
    field_simp

/-- **The twin dominates the Liouville row:** `c'_ε(d) ≥ (ρ_ε/U_1) μ²(d) d^{-ε}`. -/
theorem parityTwinWeight_ge {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : Squarefree d) :
    dampedDensity ε / parityTwinCoprimeMass ε 1 * (d : ℝ) ^ (-ε) ≤ parityTwinWeight ε d := by
  unfold parityTwinWeight
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (rpow_neg_le_mul_parityTwinShape hε hd)
    (div_nonneg (RHTower.pmPowerDampedDivisorDensity_re_pos hε).le
      (parityTwinCoprimeMass_one_pos hε).le)

/-- The damped coefficients in closed form: `w_ε(e) = ρ_ε μ(e)/D_ε(e)`. -/
theorem dampedRamanujanCoeff_eq_closed {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    dampedRamanujanCoeff ε e =
      dampedDensity ε * (moebius e : ℝ) / RHTower.pmPowerDampedRamanujanDenominator ε e := by
  rw [dampedRamanujanCoeff, RHTower.pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re]

/-- **The twin is the parity involution of the damped weight on moduli:**
`W_{c'_ε}(e) = μ(e) w_ε(e)`, with the series converging. -/
theorem hasSum_parityTwin_ramanujan {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    HasSum (fun k : ℕ => parityTwinWeight ε (e * k) / ((e * k : ℕ) : ℝ))
      ((moebius e : ℝ) * dampedRamanujanCoeff ε e) := by
  set K := dampedDensity ε / parityTwinCoprimeMass ε 1 with hK
  have hterm : (fun k : ℕ => parityTwinWeight ε (e * k) / ((e * k : ℕ) : ℝ)) =
      fun k => K * (if Nat.Coprime k e then parityTwinShape ε e * parityTwinShape ε k else 0) := by
    funext k
    rw [parityTwinWeight_div, parityTwinShape_mul]
    by_cases hc : Nat.Coprime k e
    · rw [if_pos hc.symm, if_pos hc]
    · rw [if_neg (fun h => hc h.symm), if_neg hc]
  have hs : Summable (fun k : ℕ =>
      if Nat.Coprime k e then parityTwinShape ε e * parityTwinShape ε k else 0) := by
    refine ((summable_parityTwinCoprime hε e).mul_left (parityTwinShape ε e)).congr fun k => ?_
    split_ifs <;> simp
  have hsum : ∑' k : ℕ, (if Nat.Coprime k e then parityTwinShape ε e * parityTwinShape ε k else 0) =
      parityTwinShape ε e * parityTwinCoprimeMass ε e := by
    rw [parityTwinCoprimeMass, ← tsum_mul_left]
    exact tsum_congr fun k => by split_ifs <;> simp
  suffices hval : (moebius e : ℝ) * dampedRamanujanCoeff ε e =
      K * (parityTwinShape ε e * parityTwinCoprimeMass ε e) by
    rw [hterm, hval, ← hsum]
    exact hs.hasSum.mul_left K
  rw [dampedRamanujanCoeff_eq_closed hε]
  by_cases hsq : Squarefree e
  · have hmu : (moebius e : ℝ) * (moebius e : ℝ) = 1 := by
      have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      exact_mod_cast (by simpa [sq] using this)
    have hU := parityTwinCoprimeMass_one_eq hε hsq
    have hUe := parityTwinCoprimeMass_pos hε hsq
    have hU1 := parityTwinCoprimeMass_one_pos hε
    have hD := RHTower.pmPowerDampedRamanujanDenominator_pos hε e
    set D := RHTower.pmPowerDampedRamanujanDenominator ε e with hDdef
    set PF := ∏ p ∈ e.primeFactors, (1 + parityTwinLocal ε p)
    have hP : 0 < PF :=
      prod_pos fun p hp => by linarith [parityTwinLocal_pos hε (Nat.prime_of_mem_primeFactors hp)]
    have hshape : parityTwinShape ε e * D = PF := by
      rw [parityTwinShape, if_pos hsq, hDdef]
      unfold RHTower.pmPowerDampedRamanujanDenominator
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun p hp => ?_
      have h2 := two_lt_prime_rpow hε (Nat.prime_of_mem_primeFactors hp)
      have ha : (p : ℝ) ^ (1 + ε) - 2 ≠ 0 := by linarith
      unfold parityTwinLocal
      field_simp
      ring
    have hsh : parityTwinShape ε e = PF / D := by rw [eq_div_iff hD.ne']; exact hshape
    have hL : (moebius e : ℝ) * (dampedDensity ε * (moebius e : ℝ) / D) = dampedDensity ε / D := by
      rw [show (moebius e : ℝ) * (dampedDensity ε * (moebius e : ℝ) / D) =
        dampedDensity ε * ((moebius e : ℝ) * (moebius e : ℝ)) / D by ring, hmu, mul_one]
    have hR : dampedDensity ε / (parityTwinCoprimeMass ε e * PF) *
        (PF / D * parityTwinCoprimeMass ε e) = dampedDensity ε / D := by
      have h1 := hUe.ne'
      have h2 := hP.ne'
      have h3 := hD.ne'
      field_simp
    rw [hL, hK, hU, hsh, hR]
  · rw [parityTwinShape, if_neg hsq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

theorem weightRamanujanCoeff_parityTwin {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    weightRamanujanCoeff (parityTwinWeight ε) e = (moebius e : ℝ) * dampedRamanujanCoeff ε e :=
  (hasSum_parityTwin_ramanujan hε e).tsum_eq

/-- The damped weight's own Ramanujan coefficients are `w_ε`. -/
theorem weightRamanujanCoeff_pmPowerDamped {ε : ℝ} (hε : 0 < ε) {e : ℕ} (he : 0 < e) :
    weightRamanujanCoeff (pmPowerDampedRealWeight ε) e = dampedRamanujanCoeff ε e :=
  (hasSum_dampedRamanujanCoeff hε he).tsum_eq

/-- **Identical Ramanujan amplitudes.** `|W_{c'_ε}(e)| = |W_{c_ε}(e)|` for every modulus. -/
theorem abs_weightRamanujanCoeff_parityTwin {ε : ℝ} (hε : 0 < ε) {e : ℕ} (he : 0 < e) :
    |weightRamanujanCoeff (parityTwinWeight ε) e| =
      |weightRamanujanCoeff (pmPowerDampedRealWeight ε) e| := by
  rw [weightRamanujanCoeff_parityTwin hε e, weightRamanujanCoeff_pmPowerDamped hε he, abs_mul]
  by_cases hsq : Squarefree e
  · rw [show |(moebius e : ℝ)| = 1 by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq, one_mul]
  · rw [dampedRamanujanCoeff_eq_closed hε, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- The twin has the damped mean: `Σ_d c'_ε(d)/d = ρ_ε`. -/
theorem hasSum_parityTwinWeight_div {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun d : ℕ => parityTwinWeight ε d / d) (dampedDensity ε) := by
  have h := hasSum_parityTwin_ramanujan hε 1
  simp only [one_mul, ArithmeticFunction.moebius_apply_one, Int.cast_one] at h
  rwa [dampedRamanujanCoeff_one hε] at h

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
