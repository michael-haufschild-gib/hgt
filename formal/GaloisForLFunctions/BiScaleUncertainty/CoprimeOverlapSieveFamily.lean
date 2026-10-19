import GaloisForLFunctions.BiScaleUncertainty.SieveHalfPeriodTranslation
import GaloisForLFunctions.BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression

/-!
# Actual sieve families with three overlapping coprime orders

Ramanujan inversion realizes arbitrary real coordinates on `2pq,2pr,2qr`.
The orders form an antichain, so affine data give exactly their squares and
force every possible sieve partner into this family. The odd block product
is an exact antiperiod, making the common sign a literal translation.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CoprimeOverlap
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Three nontrivial odd coprime blocks supporting overlapping sieve modes. -/
structure Triangle where
  p : ℕ
  q : ℕ
  r : ℕ
  hp : Odd p
  hq : Odd q
  hr : Odd r
  p_gt : 1 < p
  q_gt : 1 < q
  r_gt : 1 < r
  hpq : Nat.Coprime p q
  hpr : Nat.Coprime p r
  hqr : Nat.Coprime q r

namespace Triangle

def order (D : Triangle) : Fin 3 → ℕ := ![2*D.p*D.q,2*D.p*D.r,2*D.q*D.r]

def cutoff (D : Triangle) (n : ℕ) : ℕ :=
  max (D.order 0) (max (D.order 1) (D.order 2)) + n

def oddPart (D : Triangle) : Fin 3 → ℕ := ![D.p*D.q,D.p*D.r,D.q*D.r]

theorem oddPart_odd (D : Triangle) (i : Fin 3) : Odd (D.oddPart i) := by
  fin_cases i
  · exact D.hp.mul D.hq
  · exact D.hp.mul D.hr
  · exact D.hq.mul D.hr

theorem order_eq_oddPart (D : Triangle) (i : Fin 3) : D.order i = 2^1*D.oddPart i := by
  fin_cases i <;> dsimp [order,oddPart] <;> ring

theorem order_pos (D : Triangle) (i : Fin 3) : 0 < D.order i := by
  have hp : 0 < D.p := by have := D.p_gt; omega
  have hq : 0 < D.q := by have := D.q_gt; omega
  have hr : 0 < D.r := by have := D.r_gt; omega
  fin_cases i <;> dsimp [order] <;> positivity

theorem order_mem (D : Triangle) (n : ℕ) (i : Fin 3) :
    D.order i ∈ Finset.Icc 1 (D.cutoff n) := by
  refine Finset.mem_Icc.mpr ⟨D.order_pos i,?_⟩
  have h0 := le_max_left (D.order 0) (max (D.order 1) (D.order 2))
  have h1 := le_trans (le_max_left (D.order 1) (D.order 2))
    (le_max_right (D.order 0) (max (D.order 1) (D.order 2)))
  have h2 := le_trans (le_max_right (D.order 1) (D.order 2))
    (le_max_right (D.order 0) (max (D.order 1) (D.order 2)))
  unfold cutoff
  fin_cases i
  · change D.order 0 ≤ _
    omega
  · change D.order 1 ≤ _
    omega
  · change D.order 2 ≤ _
    omega

private theorem le_twice_mul (a b : ℕ) (hb : 0 < b) : a ≤ 2*a*b := by
  have he := Nat.mul_le_mul_left a (show 1 ≤ b by omega)
  simp only [mul_one] at he
  nlinarith

theorem base_mem (D : Triangle) (n : ℕ) :
    2 ≤ D.cutoff n ∧ D.p ∈ Finset.Icc 1 (D.cutoff n) ∧
      D.q ∈ Finset.Icc 1 (D.cutoff n) ∧ D.r ∈ Finset.Icc 1 (D.cutoff n) := by
  have hp : 0 < D.p := by have := D.p_gt; omega
  have hq : 0 < D.q := by have := D.q_gt; omega
  have hr : 0 < D.r := by have := D.r_gt; omega
  have h0 := (Finset.mem_Icc.mp (D.order_mem n 0)).2
  have h1 := (Finset.mem_Icc.mp (D.order_mem n 1)).2
  change 2*D.p*D.q ≤ D.cutoff n at h0
  change 2*D.p*D.r ≤ D.cutoff n at h1
  refine ⟨?_,Finset.mem_Icc.mpr ⟨hp,?_⟩,Finset.mem_Icc.mpr ⟨hq,?_⟩,
    Finset.mem_Icc.mpr ⟨hr,?_⟩⟩
  · have he := Nat.mul_pos hp hq
    nlinarith
  · exact (le_twice_mul D.p D.q hq).trans h0
  · have he := le_twice_mul D.q D.p hp
    nlinarith
  · have he := le_twice_mul D.r D.p hp
    nlinarith

private theorem not_dvd_of_exclusive {t A B : ℕ} (ht : 1 < t)
    (hA : t ∣ A) (hB : Nat.Coprime t B) : ¬ A ∣ B := by
  intro h
  have he := Nat.eq_one_of_dvd_coprimes hB (dvd_refl t) (hA.trans h)
  omega

/-- Each pair of active orders has an exclusive coprime factor. -/
theorem order_not_dvd (D : Triangle) (i j : Fin 3) (hij : i ≠ j) :
    ¬ D.order i ∣ D.order j := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact not_dvd_of_exclusive D.q_gt ⟨2*D.p,by dsimp [order]; ring⟩
      ((D.hq.coprime_two_right.mul_right D.hpq.symm).mul_right D.hqr)
  · exact not_dvd_of_exclusive D.p_gt ⟨2*D.q,by dsimp [order]; ring⟩
      ((D.hp.coprime_two_right.mul_right D.hpq).mul_right D.hpr)
  · exact not_dvd_of_exclusive D.r_gt ⟨2*D.p,by dsimp [order]; ring⟩
      ((D.hr.coprime_two_right.mul_right D.hpr.symm).mul_right D.hqr.symm)
  · exact (hij rfl).elim
  · exact not_dvd_of_exclusive D.p_gt ⟨2*D.r,by dsimp [order]; ring⟩
      ((D.hp.coprime_two_right.mul_right D.hpq).mul_right D.hpr)
  · exact not_dvd_of_exclusive D.r_gt ⟨2*D.q,by dsimp [order]; ring⟩
      ((D.hr.coprime_two_right.mul_right D.hpr.symm).mul_right D.hqr.symm)
  · exact not_dvd_of_exclusive D.q_gt ⟨2*D.r,by dsimp [order]; ring⟩
      ((D.hq.coprime_two_right.mul_right D.hpq.symm).mul_right D.hqr)
  · exact (hij rfl).elim

theorem order_injective (D : Triangle) : Function.Injective D.order := by
  intro i j he
  by_contra hij
  exact D.order_not_dvd i j hij (he ▸ dvd_refl _)

def profile (D : Triangle) (a : Fin 3 → ℝ) (q : ℕ) : ℝ :=
  ∑ i, if D.order i = q then a i else 0

theorem profile_order (D : Triangle) (a : Fin 3 → ℝ) (i : Fin 3) :
    D.profile a (D.order i) = a i := by
  simp only [profile,D.order_injective.eq_iff]
  simp

theorem profile_zero (D : Triangle) (a : Fin 3 → ℝ) (q : ℕ)
    (hq : ∀ i, q ≠ D.order i) : D.profile a q = 0 := by
  unfold profile
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (Ne.symm (hq i))

theorem profile_neg (D : Triangle) (a : Fin 3 → ℝ) (q : ℕ) :
    D.profile (fun i => -a i) q = -D.profile a q := by
  simp only [profile,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Existing Ramanujan inversion realizes the three prescribed coordinates. -/
def weights (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (D.profile a) (D.cutoff n)

theorem coordinate_weights (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (q : ℕ) :
    selbergMultiplesCoord (D.cutoff n) (D.weights n a) q = D.profile a q := by
  rw [weights,selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Finset.Icc 1 (D.cutoff n)
  · rw [if_pos hq]
  · rw [if_neg hq]
    symm
    apply D.profile_zero
    intro i he
    exact hq (he ▸ D.order_mem n i)

theorem coordinate_weights_order (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (i : Fin 3) :
    selbergMultiplesCoord (D.cutoff n) (D.weights n a) (D.order i) = a i := by
  rw [D.coordinate_weights,D.profile_order]

theorem weights_neg (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (d : ℕ) :
    D.weights n (fun i => -a i) d = -D.weights n a d := by
  simp only [weights,RHTower.pmRamanujanResidueCoeff,D.profile_neg,mul_neg,
    Finset.sum_neg_distrib]

theorem signal_neg (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (k : ℕ) :
    sieveSeq (D.cutoff n) (D.weights n (fun i => -a i)) k =
      -sieveSeq (D.cutoff n) (D.weights n a) k := by
  simp only [sieveSeq,D.weights_neg,Finset.sum_neg_distrib]

/-- The odd common factor is the actual sign-reversing shift. -/
def halfPeriod (D : Triangle) : ℕ := D.p*D.q*D.r

theorem halfPeriod_odd (D : Triangle) : Odd D.halfPeriod := (D.hp.mul D.hq).mul D.hr

theorem order_dvd_twice_halfPeriod (D : Triangle) (i : Fin 3) :
    D.order i ∣ 2*D.halfPeriod := by
  fin_cases i
  · exact ⟨D.r,by dsimp [order,halfPeriod]; ring⟩
  · exact ⟨D.q,by dsimp [order,halfPeriod]; ring⟩
  · exact ⟨D.p,by dsimp [order,halfPeriod]; ring⟩

theorem two_dvd_order (D : Triangle) (i : Fin 3) : 2 ∣ D.order i := by
  fin_cases i
  · exact ⟨D.p*D.q,by dsimp [order]; ring⟩
  · exact ⟨D.p*D.r,by dsimp [order]; ring⟩
  · exact ⟨D.q*D.r,by dsimp [order]; ring⟩

theorem signal_periodic (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) :
    Function.Periodic (sieveSeq (D.cutoff n) (D.weights n a)) (2*D.halfPeriod) := by
  apply (sieveSeq_periodic_iff_active_divisors _ _ _).mpr
  intro d _ hd
  by_contra hdiv
  apply hd
  have hz (m : ℕ) : D.profile a (d*m) = 0 := by
    apply D.profile_zero
    intro i he
    apply hdiv
    exact (show d ∣ D.order i from ⟨m,he.symm⟩).trans (D.order_dvd_twice_halfPeriod i)
  simp only [weights,RHTower.pmRamanujanResidueCoeff,hz,mul_zero,Finset.sum_const_zero]

private theorem signal_eq_on (N : ℕ) (c e : ℕ → ℝ)
    (he : ∀ d ∈ Finset.Icc 1 N, c d = e d) (k : ℕ) :
    sieveSeq N c k = sieveSeq N e k := by
  unfold sieveSeq
  apply Finset.sum_congr rfl
  intro d hd
  exact he d (Finset.mem_filter.mp hd).1

private theorem reflection_weights (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) :
    ∀ d ∈ Finset.Icc 1 (D.cutoff n),
      HalfPeriod.reflection (D.cutoff n) D.halfPeriod (D.weights n a) d =
        D.weights n (fun i => -a i) d := by
  apply (sieve_active_coefficients_eq_iff _ _ _).mpr
  intro q _
  rw [HalfPeriod.coordinate_reflection,D.coordinate_weights,D.coordinate_weights,D.profile_neg]
  by_cases hq : q ∣ D.halfPeriod
  · rw [if_pos hq]
    have hz : D.profile a q = 0 := by
      apply D.profile_zero
      intro i he
      have htwo : 2 ∣ D.halfPeriod := (D.two_dvd_order i).trans (he ▸ hq)
      obtain ⟨j,hj⟩ := htwo
      obtain ⟨k,hk⟩ := D.halfPeriod_odd
      omega
    rw [hz,neg_zero]
  · rw [if_neg hq]

/-- Negation of every coordinate is a literal integer translate, including zero support. -/
theorem signal_antiperiod (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) (k : ℕ) :
    sieveSeq (D.cutoff n) (D.weights n a) (k+D.halfPeriod) =
      -sieveSeq (D.cutoff n) (D.weights n a) k := by
  rw [← HalfPeriod.sieveSeq_reflection _ _ _ _ (D.signal_periodic n a),
    signal_eq_on _ _ _ (D.reflection_weights n a),D.signal_neg]

/-- Every translated observation preserves the common coordinate sign. -/
theorem moment_neg (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ) {m : ℕ} (h : Fin m → ℕ) :
    translatedMoment (D.cutoff n) (D.weights n (fun i => -a i)) h =
      translatedMoment (D.cutoff n) (D.weights n a) h := by
  have he := HalfPeriod.translatedMoment_reflection _ _ _ (D.signal_periodic n a) h
  unfold translatedMoment at he ⊢
  simpa only [signal_eq_on _ _ _ (D.reflection_weights n a)] using he

/-- All odd translated observations vanish on the entire overlap family. -/
theorem odd_moment_zero (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ)
    (m : ℕ) (h : Fin (2*m+1) → ℕ) :
    translatedMoment (D.cutoff n) (D.weights n a) h = 0 := by
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq,Complex.ofReal_zero]
  apply translationMoment_of_antiperiodic _ (D.halfPeriod : ZMod (D.cutoff n).factorial)
  intro x
  have hx : x+(D.halfPeriod : ZMod (D.cutoff n).factorial) =
      ((x.val+D.halfPeriod : ℕ) : ZMod (D.cutoff n).factorial) := by simp
  rw [hx,residueSignal_sieveSeq,D.signal_antiperiod]
  have he := residueSignal_sieveSeq (D.cutoff n) (D.weights n a) x.val
  rw [ZMod.natCast_zmod_val] at he
  rw [he]
  simp

private theorem profile_product_of_squares (D : Triangle) (a b : Fin 3 → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) (q d : ℕ) (hdq : d ∣ q) :
    D.profile a q * D.profile a d = D.profile b q * D.profile b d := by
  by_cases hq : ∃ i, q = D.order i
  · obtain ⟨i,rfl⟩ := hq
    by_cases hd : ∃ j, d = D.order j
    · obtain ⟨j,rfl⟩ := hd
      have hji : j = i := by
        by_contra hji
        exact D.order_not_dvd j i hji hdq
      subst j
      simpa only [D.profile_order,pow_two] using hsq i
    · have hd' : ∀ j, d ≠ D.order j := by simpa only [not_exists] using hd
      rw [D.profile_zero a d hd',D.profile_zero b d hd',mul_zero,mul_zero]
  · have hq' : ∀ i, q ≠ D.order i := by simpa only [not_exists] using hq
    rw [D.profile_zero a q hq',D.profile_zero b q hq',zero_mul,zero_mul]

/-- Every labelled affine observation supplies precisely the three coordinate squares. -/
theorem affine_iff_squares (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ) :
    (∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t =
      affineMoment (D.cutoff n) (D.weights n b) s t) ↔
        ∀ i, (a i)^2 = (b i)^2 := by
  rw [affineMoment_eq_iff_comparable]
  constructor
  · intro h i
    have he := h (D.order i) (D.order_mem n i) (D.order i)
      (Nat.mem_divisors.mpr ⟨dvd_refl _,Nat.ne_of_gt (D.order_pos i)⟩)
    simpa only [D.coordinate_weights_order,pow_two] using he
  · intro h q _ d hd
    simp only [D.coordinate_weights]
    exact D.profile_product_of_squares a b h q d (Nat.dvd_of_mem_divisors hd)

theorem coordinate_squares (D : Triangle) (n : ℕ) (a b : Fin 3 → ℝ)
    (hsq : ∀ i, (a i)^2 = (b i)^2) (q : ℕ) :
    selbergMultiplesCoord (D.cutoff n) (D.weights n a) q ^ 2 =
      selbergMultiplesCoord (D.cutoff n) (D.weights n b) q ^ 2 := by
  simpa only [D.coordinate_weights,pow_two] using
    D.profile_product_of_squares a b hsq q q (dvd_refl q)

/-- Affine data force every arbitrary sieve partner back into the realized three-mode family. -/
theorem affine_partner_realization (D : Triangle) (n : ℕ) (a : Fin 3 → ℝ)
    (e : ℕ → ℝ)
    (haff : ∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t =
      affineMoment (D.cutoff n) e s t) :
    ∃ b : Fin 3 → ℝ, ∀ k, sieveSeq (D.cutoff n) e k =
      sieveSeq (D.cutoff n) (D.weights n b) k := by
  let b : Fin 3 → ℝ := fun i => selbergMultiplesCoord (D.cutoff n) e (D.order i)
  refine ⟨b,?_⟩
  have hc := (affineMoment_eq_iff_comparable (D.cutoff n) (D.weights n a) e).mp haff
  have hw : ∀ d ∈ Finset.Icc 1 (D.cutoff n), e d = D.weights n b d := by
    apply (sieve_active_coefficients_eq_iff _ _ _).mpr
    intro q hq
    by_cases hm : ∃ i, q = D.order i
    · obtain ⟨i,rfl⟩ := hm
      rw [D.coordinate_weights_order]
    · have hm' : ∀ i, q ≠ D.order i := by simpa only [not_exists] using hm
      have he := hc q hq q (Nat.mem_divisors.mpr
        ⟨dvd_refl q,by have := (Finset.mem_Icc.mp hq).1; omega⟩)
      rw [D.coordinate_weights,D.profile_zero a q hm',zero_mul] at he
      have hz : selbergMultiplesCoord (D.cutoff n) e q = 0 := mul_self_eq_zero.mp he.symm
      rw [hz,D.coordinate_weights,D.profile_zero b q hm']
  exact signal_eq_on _ _ _ hw

end Triangle
end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CoprimeOverlap
