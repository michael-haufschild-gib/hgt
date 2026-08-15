import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusCrossPairStrictGammaBVDescent

/-!
# Singular one-leg trace of the coherent cross-pair source

The four-label Frobenius source requires contraction of its right ordered-edge
leg by algebraic summation. This module constructs that contraction on the
finite-support packet, embeds the packet faithfully into the actual
Calderón--Witt `ℓ²` edge completion, and proves that no continuous linear
functional on the completion extends the algebraic sum.

Normalized indicators of `N` distinct edge coordinates have Hilbert norm one
but algebraic one-leg trace `sqrt N`; hence extension is impossible. The
finite coherent Frobenius fiber factors exactly through this singular trace,
not merely through a post-hoc zero identity. This identifies the analytic
frontier precisely: a successful cofinal descent must define and control a
genuinely singular/nonclosable one-leg trace on the source domain. No RH,
zero-location, positivity, spectral-synthesis, or computation premise occurs.
-/

open Complex Filter Function Set Topology
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

noncomputable local instance instDecidableEqCrossPrimePacketIndexOneLegTrace :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

def deningerBigWittCrossPairNthPrime (n : ℕ) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime n,
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n⟩

theorem deningerBigWittCrossPairNthPrime_val_strictMono :
    StrictMono (fun n => (deningerBigWittCrossPairNthPrime n : ℕ)) := by
  intro m n hmn
  exact (Nat.nth_strictMono Nat.infinite_setOf_prime hmn)

def deningerBigWittCrossPairPacketNatEmbedding : ℕ ↪ DeningerCalderonWittCrossPrimePacketIndex where
  toFun n := ⟨(deningerBigWittCrossPairNthPrime n, deningerBigWittCrossPairNthPrime (n + 1)),
    by
      intro h
      exact (Nat.ne_of_lt (deningerBigWittCrossPairNthPrime_val_strictMono (Nat.lt_succ_self n)))
        (congrArg Subtype.val h)⟩
  inj' := by
    intro m n h
    have hfirst : deningerBigWittCrossPairNthPrime m = deningerBigWittCrossPairNthPrime n :=
      congrArg (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.1) h
    exact deningerBigWittCrossPairNthPrime_val_strictMono.injective (congrArg Subtype.val hfirst)

local instance instInfiniteCrossPrimePacketIndexOneLegTrace :
    Infinite DeningerCalderonWittCrossPrimePacketIndex :=
  Infinite.of_injective deningerBigWittCrossPairPacketNatEmbedding deningerBigWittCrossPairPacketNatEmbedding.injective

def deningerBigWittCrossPairPacketIndicator
    (T : Finset DeningerCalderonWittCrossPrimePacketIndex) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  ∑ i ∈ T, lp.single 2 i (((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹)

theorem deningerBigWittCrossPairPacketIndicator_apply
    (T : Finset DeningerCalderonWittCrossPrimePacketIndex)
    (j : DeningerCalderonWittCrossPrimePacketIndex) :
    (deningerBigWittCrossPairPacketIndicator T :
      DeningerCalderonWittCrossPrimePacketIndex → ℂ) j =
      if j ∈ T then ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹ else 0 := by
  classical
  rw [deningerBigWittCrossPairPacketIndicator]
  rw [lp.coeFn_sum, Finset.sum_apply]
  rw [show (fun i =>
      (lp.single 2 i (((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹) :
        DeningerCalderonWittCrossPrimePacketIndex → ℂ) j) =
      fun i => if j = i then
        (((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹) else 0 by
    funext i
    rw [lp.single_apply, Pi.single_apply]]
  simp

theorem norm_deningerBigWittCrossPairPacketIndicator
    {T : Finset DeningerCalderonWittCrossPrimePacketIndex}
    (hT : T.Nonempty) :
    ‖deningerBigWittCrossPairPacketIndicator T‖ = 1 := by
  have hcard : (0 : ℝ) < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T.card : ℝ) := Real.sqrt_pos.mpr hcard
  have hsq : ‖deningerBigWittCrossPairPacketIndicator T‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rw [show (fun j : DeningerCalderonWittCrossPrimePacketIndex =>
        ‖(deningerBigWittCrossPairPacketIndicator T :
          DeningerCalderonWittCrossPrimePacketIndex → ℂ) j‖ ^ 2) =
        fun j => if j ∈ T then (Real.sqrt (T.card : ℝ))⁻¹ ^ 2 else 0 by
      funext j
      rw [deningerBigWittCrossPairPacketIndicator_apply]
      by_cases hj : j ∈ T <;>
        simp [hj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsqrt]]
    rw [tsum_eq_sum (s := T) (fun j hj => by simp [hj])]
    rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
      nsmul_eq_mul, inv_pow, Real.sq_sqrt hcard.le]
    field_simp
  nlinarith [norm_nonneg (deningerBigWittCrossPairPacketIndicator T), hsq]

theorem deningerBigWittCrossPairOneLegTrace_packetIndicator
    {T : Finset DeningerCalderonWittCrossPrimePacketIndex}
    (hT : T.Nonempty) :
    ∑ _i ∈ T, ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹ =
      ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) := by
  have hcard : (0 : ℝ) < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T.card : ℝ) := Real.sqrt_pos.mpr hcard
  have hne : ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simpa using hsqrt.ne'
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show ((T.card : ℕ) : ℂ) =
      ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) ^ 2 by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hcard.le]
    norm_cast]
  field_simp

theorem not_exists_bounded_deningerBigWittCrossPairOneLegTrace :
    ¬ ∃ ell : DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ] ℂ,
        ∀ (T : Finset DeningerCalderonWittCrossPrimePacketIndex)
          (c : DeningerCalderonWittCrossPrimePacketIndex → ℂ),
          ell (∑ i ∈ T, lp.single 2 i (c i)) = ∑ i ∈ T, c i := by
  rintro ⟨ell, hell⟩
  obtain ⟨T, hTcard⟩ :=
    Infinite.exists_subset_card_eq DeningerCalderonWittCrossPrimePacketIndex
      (⌊‖ell‖ ^ 2⌋₊ + 1)
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    omega
  have hlarge : ‖ell‖ ^ 2 < (T.card : ℝ) := by
    rw [hTcard]
    push_cast
    exact Nat.lt_floor_add_one (‖ell‖ ^ 2)
  have hvalue : ell (deningerBigWittCrossPairPacketIndicator T) =
      ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) := by
    rw [deningerBigWittCrossPairPacketIndicator,
      hell T (fun _ => ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹)]
    exact deningerBigWittCrossPairOneLegTrace_packetIndicator hTne
  have hbound : ‖ell (deningerBigWittCrossPairPacketIndicator T)‖ ≤ ‖ell‖ := by
    have h := ell.le_opNorm (deningerBigWittCrossPairPacketIndicator T)
    rwa [norm_deningerBigWittCrossPairPacketIndicator hTne, mul_one] at h
  rw [hvalue, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hbound
  have hsq : Real.sqrt (T.card : ℝ) ^ 2 = (T.card : ℝ) :=
    Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg ell, Real.sqrt_nonneg (T.card : ℝ)]

def deningerBigWittCrossPairAlgebraicOneLegTrace :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun _ => LinearMap.id)

@[simp] theorem deningerBigWittCrossPairAlgebraicOneLegTrace_single
    (i : DeningerCalderonWittCrossPrimePacketIndex) (z : ℂ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (Finsupp.single i z) = z := by
  classical
  simp [deningerBigWittCrossPairAlgebraicOneLegTrace, Finsupp.lsum]

def deningerBigWittCrossPairFinitePacketAdmissionToFun
    (c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  ∑ i ∈ c.support, lp.single 2 i (c i)

theorem deningerBigWittCrossPairFinitePacketAdmissionToFun_apply
    (c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (j : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairFinitePacketAdmissionToFun c j = c j := by
  classical
  rw [deningerBigWittCrossPairFinitePacketAdmissionToFun, lp.coeFn_sum, Finset.sum_apply]
  rw [show (fun i =>
      (lp.single 2 i (c i) :
        DeningerCalderonWittCrossPrimePacketIndex → ℂ) j) =
      fun i => if j = i then c i else 0 by
    funext i
    rw [lp.single_apply, Pi.single_apply]]
  by_cases hj : j ∈ c.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [Ne.symm hij]
    · exact fun h => (h hj).elim
  · rw [Finset.sum_eq_zero]
    · have hcj : c j = 0 := by
        by_contra hne
        exact hj (Finsupp.mem_support_iff.mpr hne)
      exact hcj.symm
    · intro i hi
      simp only [ite_eq_right_iff]
      intro hji
      subst i
      exact False.elim (hj hi)

def deningerBigWittCrossPairFinitePacketAdmission :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert where
  toFun := deningerBigWittCrossPairFinitePacketAdmissionToFun
  map_add' c d := by
    apply lp.ext
    funext j
    change deningerBigWittCrossPairFinitePacketAdmissionToFun (c + d) j =
      deningerBigWittCrossPairFinitePacketAdmissionToFun c j +
        deningerBigWittCrossPairFinitePacketAdmissionToFun d j
    rw [deningerBigWittCrossPairFinitePacketAdmissionToFun_apply,
      deningerBigWittCrossPairFinitePacketAdmissionToFun_apply,
      deningerBigWittCrossPairFinitePacketAdmissionToFun_apply, Finsupp.add_apply]
  map_smul' z c := by
    apply lp.ext
    funext j
    change deningerBigWittCrossPairFinitePacketAdmissionToFun (z • c) j =
      z * deningerBigWittCrossPairFinitePacketAdmissionToFun c j
    rw [deningerBigWittCrossPairFinitePacketAdmissionToFun_apply,
      deningerBigWittCrossPairFinitePacketAdmissionToFun_apply, Finsupp.smul_apply]
    rfl

@[simp] theorem deningerBigWittCrossPairFinitePacketAdmission_single
    (i : DeningerCalderonWittCrossPrimePacketIndex) (z : ℂ) :
    deningerBigWittCrossPairFinitePacketAdmission (Finsupp.single i z) = lp.single 2 i z := by
  apply lp.ext
  funext j
  rw [show (deningerBigWittCrossPairFinitePacketAdmission (Finsupp.single i z)) j =
      (Finsupp.single i z) j by
    exact deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _]
  rw [lp.single_apply, Pi.single_apply, Finsupp.single_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

theorem deningerBigWittCrossPairAlgebraicOneLegTrace_noContinuousExtension :
    ¬ ∃ ell : DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ] ℂ,
      ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
        ell (deningerBigWittCrossPairFinitePacketAdmission c) =
          deningerBigWittCrossPairAlgebraicOneLegTrace c := by
  intro h
  apply not_exists_bounded_deningerBigWittCrossPairOneLegTrace
  rcases h with ⟨ell, hell⟩
  refine ⟨ell, ?_⟩
  intro T c
  let x : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
    ∑ i ∈ T, Finsupp.single i (c i)
  have hx := hell x
  simpa only [x, map_sum, deningerBigWittCrossPairFinitePacketAdmission_single,
    deningerBigWittCrossPairAlgebraicOneLegTrace_single] using hx

def deningerBigWittCrossPairFiniteRightLegPacket
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  ∑ r ∈ s, ∑ t ∈ s,
    if hrt : r ≠ t then
      Finsupp.single ⟨(r, t), hrt⟩
        (deningerBigWittCrossPairRightLeg a r t)
    else 0

theorem deningerBigWittCrossPairAlgebraicOneLegTrace_finiteRightLegPacket_eq_total
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCrossPairFiniteRightLegPacket a s) =
      ∑ r ∈ s, ∑ t ∈ s,
        deningerBigWittCrossPairRightLeg a r t := by
  classical
  rw [deningerBigWittCrossPairFiniteRightLegPacket]
  simp only [map_sum]
  have hsum :
      (∑ r ∈ s, ∑ t ∈ s,
        deningerBigWittCrossPairAlgebraicOneLegTrace
          (if hrt : r ≠ t then
            Finsupp.single ⟨(r, t), hrt⟩
              (deningerBigWittCrossPairRightLeg a r t)
          else 0)) =
      ∑ r ∈ s, ∑ t ∈ s,
        deningerBigWittCrossPairRightLeg a r t := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hrt : r ≠ t
    · rw [dif_pos hrt, deningerBigWittCrossPairAlgebraicOneLegTrace_single]
    · rw [dif_neg hrt, map_zero]
      have hEq : r = t := not_ne_iff.mp hrt
      subst t
      simp [deningerBigWittCrossPairRightLeg]
  exact hsum

theorem deningerBigWittCrossPairAlgebraicOneLegTrace_finiteRightLegPacket
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCrossPairFiniteRightLegPacket a s) = 0 := by
  rw [deningerBigWittCrossPairAlgebraicOneLegTrace_finiteRightLegPacket_eq_total,
    deningerBigWittCrossPairRightLeg_total_zero]

theorem deningerBigWittCrossPairFrobeniusFiberCoefficient_eq_singularOneLegContraction
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusFiberCoefficient a s p q =
      (-2 * deningerBigWittCrossPairLeftLeg a p q) *
        deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCrossPairFiniteRightLegPacket a s) := by
  rw [deningerBigWittCrossPairFrobeniusFiberCoefficient,
    deningerBigWittCrossPairAlgebraicOneLegTrace_finiteRightLegPacket_eq_total]
  simp only [deningerBigWittCrossPairFrobeniusCoefficient_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]

def deningerBigWittCrossPairPacketPrefix
    (n : ℕ) : Finset DeningerCalderonWittCrossPrimePacketIndex :=
  (Finset.range (n + 1)).map deningerBigWittCrossPairPacketNatEmbedding

@[simp] theorem deningerBigWittCrossPairPacketPrefix_card (n : ℕ) :
    (deningerBigWittCrossPairPacketPrefix n).card = n + 1 := by
  rw [deningerBigWittCrossPairPacketPrefix, Finset.card_map, Finset.card_range]

def deningerBigWittCrossPairPacketAveragingPacket
    (n : ℕ) : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  (deningerBigWittCrossPairPacketPrefix n).sum fun i =>
    Finsupp.single i (((n + 1 : ℝ) : ℂ)⁻¹)

@[simp] theorem deningerBigWittCrossPairPacketAveragingPacket_apply
    (n : ℕ) (j : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairPacketAveragingPacket n j =
      if j ∈ deningerBigWittCrossPairPacketPrefix n then (((n + 1 : ℝ) : ℂ)⁻¹) else 0 := by
  classical
  simp [deningerBigWittCrossPairPacketAveragingPacket, Finsupp.single_apply]

@[simp] theorem deningerBigWittCrossPairAlgebraicOneLegTrace_averagingPacket (n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCrossPairPacketAveragingPacket n) = 1 := by
  classical
  rw [deningerBigWittCrossPairPacketAveragingPacket, map_sum]
  simp only [deningerBigWittCrossPairAlgebraicOneLegTrace_single,
    Finset.sum_const, nsmul_eq_mul, deningerBigWittCrossPairPacketPrefix_card]
  have hne : ((((n : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (n + 1 : ℝ) ≠ 0)
  rw [show ((n + 1 : ℕ) : ℂ) = ((((n : ℝ) + 1 : ℝ) : ℂ)) by
    norm_cast]
  exact mul_inv_cancel₀ hne

theorem norm_sq_deningerBigWittCrossPairFinitePacketAdmission_averagingPacket (n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairPacketAveragingPacket n)‖ ^ 2 =
      (n + 1 : ℝ)⁻¹ := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  rw [show (fun j : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖(deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairPacketAveragingPacket n) :
        DeningerCalderonWittCrossPrimePacketIndex → ℂ) j‖ ^ 2) =
      fun j => if j ∈ deningerBigWittCrossPairPacketPrefix n then ((n + 1 : ℝ)⁻¹) ^ 2 else 0 by
    funext j
    rw [show (deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairPacketAveragingPacket n)) j =
        deningerBigWittCrossPairPacketAveragingPacket n j by
      exact deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _]
    rw [deningerBigWittCrossPairPacketAveragingPacket_apply]
    by_cases hj : j ∈ deningerBigWittCrossPairPacketPrefix n
    · simp only [if_pos hj]
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    · simp [hj]]
  rw [tsum_eq_sum (s := deningerBigWittCrossPairPacketPrefix n) (fun j hj => by simp [hj])]
  rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
    deningerBigWittCrossPairPacketPrefix_card, nsmul_eq_mul]
  have hne : (n + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem tendsto_deningerBigWittCrossPairFinitePacketAdmission_averagingPacket :
    Tendsto (fun n =>
      deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairPacketAveragingPacket n))
      atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / epsilon ^ 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsq :
      ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairPacketAveragingPacket n)‖ ^ 2 <
        epsilon ^ 2 := by
    rw [norm_sq_deningerBigWittCrossPairFinitePacketAdmission_averagingPacket]
    have hn1 : 1 / epsilon ^ 2 < (n + 1 : ℝ) := by
      calc
        1 / epsilon ^ 2 < (N : ℝ) := by exact_mod_cast hN
        _ ≤ n := by exact_mod_cast hn
        _ < n + 1 := by norm_num
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    rw [inv_lt_iff_one_lt_mul₀ hnpos]
    have heps : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hprod : 1 < (n + 1 : ℝ) * epsilon ^ 2 :=
      (div_lt_iff₀ heps).mp hn1
    nlinarith
  nlinarith [norm_nonneg
    (deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairPacketAveragingPacket n))]

theorem tendsto_deningerBigWittCrossPairAlgebraicOneLegTrace_averagingPacket :
    Tendsto (fun n =>
      deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCrossPairPacketAveragingPacket n))
      atTop (nhds 1) := by
  simpa only [deningerBigWittCrossPairAlgebraicOneLegTrace_averagingPacket] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1))

def deningerBigWittCrossPairAlgebraicOneLegTraceReal :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℝ] ℂ :=
  deningerBigWittCrossPairAlgebraicOneLegTrace.restrictScalars ℝ

def deningerBigWittCrossPairFinitePacketAdmissionReal :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℝ]
      DeningerCalderonWittCrossPrimePacketHilbert :=
  deningerBigWittCrossPairFinitePacketAdmission.restrictScalars ℝ

theorem deningerBigWittCrossPairAlgebraicOneLegTrace_not_closable :
    ¬ IsSequentiallyClosableBetween
      deningerBigWittCrossPairAlgebraicOneLegTraceReal deningerBigWittCrossPairFinitePacketAdmissionReal := by
  exact not_isSequentiallyClosableBetween_of_exact_norm_graphNull
    deningerBigWittCrossPairAlgebraicOneLegTraceReal deningerBigWittCrossPairFinitePacketAdmissionReal
    deningerBigWittCrossPairAlgebraicOneLegTraceReal deningerBigWittCrossPairFinitePacketAdmissionReal
    (fun _ => rfl) (fun _ => rfl) deningerBigWittCrossPairPacketAveragingPacket 1
    (by simpa [deningerBigWittCrossPairFinitePacketAdmissionReal] using
      tendsto_deningerBigWittCrossPairFinitePacketAdmission_averagingPacket)
    (by exact
      tendsto_deningerBigWittCrossPairAlgebraicOneLegTrace_averagingPacket)
    one_ne_zero


end

end RHTower
