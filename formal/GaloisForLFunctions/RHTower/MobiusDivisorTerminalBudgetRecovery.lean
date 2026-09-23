import GaloisForLFunctions.RHTower.MobiusDivisorSquareRootTerminalOrder
import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport
import GaloisForLFunctions.RHTower.MobiusDivisorSignedPrimeBatches
import GaloisForLFunctions.RHTower.WoldBooleanAcceleratedType
/-!
# Prime-density control of the terminal successor envelope

A bounded remaining quotient front becomes scalar at large cutoff. Its
singleton square energy is bounded by prime density, uniformly in the
processed core. A square-root head then gives a subquadratic full successor
envelope. Opposite finite signed supplies provide a discrete head cover.
These estimates do not bound the complete signed arithmetic endpoint.
-/
noncomputable section
open Finset Filter Topology
namespace RHTower

/-- A fixed bound on every remaining quotient eventually forces the scalar terminal phase. -/
theorem mobiusDivisorSmallSelectionPrimes_subset_of_quotient
    (M J : ℕ) (P : Finset ℕ) (hM : (J+1)^(2 : ℕ) ≤ M)
    (hfront : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ J) :
    mobiusDivisorSmallSelectionPrimes M ⊆ P := by
  intro p hp
  obtain ⟨hp,hsmall⟩ := mem_filter.mp hp
  by_contra hfree
  have hquot := hfront p (mem_sdiff.mpr ⟨hp,hfree⟩)
  have hprime := (mem_filter.mp hp).2
  have hmul := (Nat.div_lt_iff_lt_mul hprime.pos).mp (show M/p < J+1 by omega)
  by_cases hle : p ≤ J+1 <;> nlinarith

private lemma singleton_abs_bound (M J : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hquot : M/p ≤ J) :
    |mobiusDivisorSelectionFibre M P {p}| ≤ (3/5:ℝ)*J*Real.sqrt M := by
  have hs := (single_le_sum (fun R (_ : R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset) =>
    abs_nonneg (mobiusDivisorSelectionFibre M P (insert p R)))
      (mem_powerset.mpr (empty_subset _))).trans
        (sum_abs_mobiusDivisorPrimeFibre_le_quotient M P hp)
  simp only [insert_empty_eq] at hs
  have hq : ((M/p:ℕ):ℝ) ≤ J := by exact_mod_cast hquot
  nlinarith only [hs,mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ (3/5)*Real.sqrt M)]

private lemma selection_card_le (M : ℕ) :
    (mobiusDivisorSelectionPrimes M).card ≤ Nat.primeCounting M := by
  change ((range M).filter Nat.Prime).card ≤ _
  rw [Nat.primeCounting,← Nat.primesBelow_card_eq_primeCounting']
  apply card_le_card
  intro p hp
  obtain ⟨hp,hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hp; omega),hprime⟩

private lemma terminal_leaf_squares_bound (M J : ℕ) (P : Finset ℕ)
    (hfront : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ J) :
    (∑ p ∈ mobiusDivisorSelectionPrimes M \ P,(mobiusDivisorSelectionFibre M P {p})^(2 : ℕ)) ≤
      (9/25:ℝ)*J^(2 : ℕ)*M*Nat.primeCounting M := by
  have hs : (∑ p ∈ mobiusDivisorSelectionPrimes M \ P,(mobiusDivisorSelectionFibre M P {p})^(2 : ℕ)) ≤
      ∑ _p ∈ mobiusDivisorSelectionPrimes M \ P,(9/25:ℝ)*J^(2 : ℕ)*M := by
    apply sum_le_sum
    intro p hp
    have hb := singleton_abs_bound M J P (mem_filter.mp (mem_sdiff.mp hp).1).2 (hfront p hp)
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
    rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg M)] at hsq
    nlinarith only [hsq]
  have hc : ((mobiusDivisorSelectionPrimes M \ P).card:ℝ) ≤ Nat.primeCounting M := by
    exact_mod_cast (card_le_card sdiff_subset).trans (selection_card_le M)
  simp only [sum_const,nsmul_eq_mul] at hs
  nlinarith only [hs,mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ (9/25)*J^(2 : ℕ)*M)]

/-- Once the head is square-root sized, the entire bounded terminal successor envelope is controlled by prime density. -/
theorem mobiusDivisorSuccessorEnvelope_le_terminal_density
    (M J : ℕ) (P : Finset ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hterminal : mobiusDivisorSmallSelectionPrimes M ⊆ P)
    (hfront : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ J)
    (hhead : |mobiusDivisorSelectionFibre M P ∅| ≤ A*Real.sqrt M) :
    mobiusDivisorSuccessorEnvelope M P ≤
      ((A+(3/5:ℝ)*J)^(2 : ℕ)+(9/25:ℝ)*J^(2 : ℕ)*Nat.primeCounting M)*M := by
  have hbound (Q : Finset ℕ) (hPQ : P ⊆ Q)
      (hh : |mobiusDivisorSelectionFibre M Q ∅| ≤ (A+(3/5:ℝ)*J)*Real.sqrt M) :
      mobiusDivisorSelectionEnergy M Q ≤
        ((A+(3/5:ℝ)*J)^(2 : ℕ)+(9/25:ℝ)*J^(2 : ℕ)*Nat.primeCounting M)*M := by
    have hs := terminal_leaf_squares_bound M J Q (fun p hp => hfront p
      (mem_sdiff.mpr ⟨(mem_sdiff.mp hp).1,fun h => (mem_sdiff.mp hp).2 (hPQ h)⟩))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
    rw [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg M)] at hsq
    rw [mobiusDivisorSelectionEnergy_terminal M Q (hterminal.trans hPQ)]
    nlinarith only [hs,hsq]
  rw [mobiusDivisorSuccessorEnvelope_le_iff]
  constructor
  · apply hbound P Subset.rfl
    exact hhead.trans (by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (3/5)*J) (Real.sqrt_nonneg (M:ℝ))])
  · intro p hp
    apply hbound (insert p P) (subset_insert p P)
    rw [mobiusDivisorSelectionFibre_insert]
    simp only [notMem_empty,if_false,insert_empty_eq]
    have hb := singleton_abs_bound M J P (mem_filter.mp (mem_sdiff.mp hp).1).2 (hfront p hp)
    exact (abs_add_le _ _).trans (by nlinarith only [hhead,hb])

private lemma prime_density_zero :
    Tendsto (fun M : ℕ => (Nat.primeCounting M:ℝ)/(M:ℝ)) atTop (nhds 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := tendsto_primeCounting_nat_ratio.mul hlog.inv_tendsto_atTop
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with M hM
  have hMr : (1:ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hlogne := (Real.log_pos hMr).ne'
  change (Nat.primeCounting M:ℝ)/((M:ℝ)/Real.log M)*(Real.log M)⁻¹ = _
  field_simp

/-- The repaired terminal envelope fits any positive quadratic budget uniformly in the processed core. -/
theorem eventually_mobiusDivisor_terminal_envelope_small
    (J : ℕ) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,∀ P : Finset ℕ,
      (∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ J) →
      |mobiusDivisorSelectionFibre M P ∅| ≤ A*Real.sqrt M →
      mobiusDivisorSuccessorEnvelope M P ≤ ε*(M:ℝ)^(2 : ℕ) := by
  have hN : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun M : ℕ =>
      (A+(3/5:ℝ)*J)^(2 : ℕ)/(M:ℝ)+(9/25:ℝ)*J^(2 : ℕ)*((Nat.primeCounting M:ℝ)/(M:ℝ))) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (hN.inv_tendsto_atTop.const_mul ((A+(3/5:ℝ)*J)^(2 : ℕ))).add
        (prime_density_zero.const_mul ((9/25:ℝ)*J^(2 : ℕ)))
  filter_upwards [hz.eventually (eventually_lt_nhds hε),
    eventually_ge_atTop ((J+1)^(2 : ℕ)),eventually_ge_atTop (1:ℕ)] with M he hM hM1
  intro P hfront hhead
  have hb := mobiusDivisorSuccessorEnvelope_le_terminal_density M J P A hA
    (mobiusDivisorSmallSelectionPrimes_subset_of_quotient M J P hM hfront) hfront hhead
  have hm : (0:ℝ) < M := by exact_mod_cast hM1
  have he' : ((A+(3/5:ℝ)*J)^(2 : ℕ)+(9/25:ℝ)*J^(2 : ℕ)*Nat.primeCounting M)/(M:ℝ) < ε := by
    simpa only [add_div,mul_div_assoc] using he
  have hh := (div_lt_iff₀ hm).mp he'
  exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_right hh.le hm.le])

/-- Opposite finite signed supplies can place the head within one source weight, whenever the target lies in their total mass interval. -/
theorem exists_signedScalarHeadCover {α : Type*} [DecidableEq α]
    (A B : Finset α) (c : α → ℝ) (h a : ℝ) (ha : 0 ≤ a)
    (hA : ∀ p ∈ A,0 ≤ c p ∧ c p ≤ a)
    (hB : ∀ p ∈ B,0 ≤ -c p ∧ -c p ≤ a)
    (hcoverA : -h ≤ ∑ p ∈ A,c p) (hcoverB : h ≤ ∑ p ∈ B,-c p) :
    ∃ L ⊆ A ∪ B, |h+∑ p ∈ L,c p| ≤ a := by
  rcases le_total 0 h with hh|hh
  · obtain ⟨L,hLB,h0,h1,_⟩ := exists_mass_cover_with_square_reserve B
      (fun p => -c p) a ha h hh hB hcoverB
    refine ⟨L,hLB.trans subset_union_right,?_⟩
    rw [sum_neg_distrib] at h0 h1
    rw [abs_of_nonpos (by linarith only [h0])]
    linarith only [h1]
  · obtain ⟨L,hLA,h0,h1,_⟩ := exists_mass_cover_with_square_reserve A c a ha
      (-h) (by linarith only [hh]) hA hcoverA
    refine ⟨L,hLA.trans subset_union_left,?_⟩
    rw [abs_of_nonneg (by linarith only [h0])]
    linarith only [h1]
end RHTower
