import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryFiniteFlipSetHasAnExactResolutionThreshold
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFlipThresholdIsSetByTheConductorsOfThePrime
import GaloisForLFunctions.BezoutValuationIncidence.NonMarkovianLagOperatorAlgebraAndPrimePowerRevival
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity

/-!
# Every low conductor sees the flip set

Flip the odd powers of the primes of a finite set `S` and let `Y_S = Π_{p∈S} F_p` be the product
trial, a Ramanujan packet `Σ_{d ∣ Q} β_d e_d` on the divisors of `Q = Π_{p∈S} p²`. Transport it to a
conductor `m` prime to `Q`: the block `e_m Y_S = Σ_d β_d e_{md}`.

* **The flip does not see the conductor** (`twistLimitEnergy_block_combination`). The flipped lags
  are powers of primes of `S`, which fix every `e_m`, and the period mean factors over the coprime
  moduli `m` and `Q`. So for `y = (Σ_m a_m e_m) Y_S`,
  `2 Σ_k d(k) k^{−1/2} M(y·y(k·)) = (Σ_m a_m²) · τ_S`, with `τ_S` the flip energy of `Y_S`.
* **Blocks are orthogonal** (`packetEnergy_block_combination`). The conductors `md` are distinct, so
  the limiting twisted energy of `Σ_m a_m (e_m Y_S)` is `Σ_m a_m² b_m`,
  `b_m = Σ_d β_d² E_{md}(c) + τ_S`.
* **Index growth** (`eventually_flip_negative_subspace`). Every set `M` of conductors prime to `Q`
  with `b_m < 0` spans a subspace of dimension `#M` on which the twisted complete Weil matrix is
  eventually negative definite.

Since `E_t(c) → 0` as `c → ∞` and `τ_S < 0`, for every `n` all large overlaps carry `n` such
blocks (`exists_overlap_flip_negIndex_ge`): the flipped complete Weil matrix has at least `n`
negative eigenvalues, while `ζ`'s is positive definite at every fixed overlap. The index of a twin
grows without bound with the resolution; one square is carried by the pole, the others by the
conductors `m ≥ 2`, which see the flip exactly as the pole does.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
  RenormalizedBiarithmeticGeometry CompletedShell ArithmeticCastelnuovoSeveri Zeta23
  ArithmeticCountingPositivity TransMetzlerWeilPositivity.BoundedOverlap
open _root_.RHTower (vonMangoldtAtom)

/-! ### Multiplicativity and coprime period means -/

/-- Normalized Ramanujan modes of coprime conductors multiply. -/
theorem normalizedRamanujanMode_mul_of_coprime {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hmd : m.Coprime d) (n : ℕ) :
    normalizedRamanujanMode (m * d) n = normalizedRamanujanMode m n * normalizedRamanujanMode d n := by
  rw [normalizedRamanujanMode_eq_coefficient (Nat.mul_pos hm hd),
    normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hd,
    BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hmd, Nat.totient_mul hmd,
    Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

/-- A period mean can be read over any multiple of the period. -/
theorem periodMean_mul_period {g : ℕ → ℝ} {P : ℕ} (hP : 0 < P) (hg : Function.Periodic g P)
    {k : ℕ} (hk : 0 < k) : periodMean g (k * P) = periodMean g P := by
  unfold periodMean
  rw [sum_range_mul_of_periodic hg k]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

/-- **The period mean factors over coprime moduli.** -/
theorem periodMean_mul_of_coprime {f g : ℕ → ℝ} {P₁ P₂ : ℕ} (h₁ : 0 < P₁) (h₂ : 0 < P₂)
    (hcop : P₁.Coprime P₂) (hf : Function.Periodic f P₁) (hg : Function.Periodic g P₂) :
    periodMean (fun a => f a * g a) (P₁ * P₂) = periodMean f P₁ * periodMean g P₂ := by
  unfold periodMean
  rw [_root_.RHTower.DeletionCoprimeWords.coprime_period_sum_mul h₁ h₂ hcop hf hg]
  push_cast
  field_simp

/-! ### Blocks -/

section Blocks

variable {S : Finset ℕ}

/-- The product of two divisors-and-conductors: `(m, d) ↦ m d` is injective on conductors prime to
`Q` times divisors of `Q`, since `d = gcd(m d, Q)`. -/
theorem mul_injOn_coprime_divisors {Q : ℕ} {M : Finset ℕ} (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime Q) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (M ×ˢ Q.divisors : Finset (ℕ × ℕ)) := by
  rintro ⟨m, d⟩ hx ⟨m', d'⟩ hx' h
  simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors] at hx hx'
  simp only at h
  have hgcd : ∀ {m d : ℕ}, m.Coprime Q → d ∣ Q → Nat.gcd (m * d) Q = d := by
    intro m d hmQ hdQ
    apply Nat.dvd_antisymm
    · have h1 : Nat.gcd (m * d) Q ∣ m * d := Nat.gcd_dvd_left _ _
      have h2 : (Nat.gcd (m * d) Q).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hmQ.symm
      exact h2.dvd_of_dvd_mul_left h1
    · exact Nat.dvd_gcd (dvd_mul_left d m) hdQ
  have hd : d = d' := by
    rw [← hgcd (hM m hx.1).2 hx.2.1, ← hgcd (hM m' hx'.1).2 hx'.2.1, h]
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hx.2.1 (Nat.pos_of_ne_zero hx.2.2)
  subst hd
  have hm : m = m' := Nat.eq_of_mul_eq_mul_right hd0 h
  rw [hm]

/-- The conductors of a block combination. -/
def blockConductors (Q : ℕ) (M : Finset ℕ) : Finset ℕ := (M ×ˢ Q.divisors).image fun x => x.1 * x.2

/-- The coefficients of the block combination `Σ_m a_m Σ_d β_d e_{md}`. -/
def blockCoeff (Q : ℕ) (M : Finset ℕ) (a β : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ x ∈ M ×ˢ Q.divisors, if x.1 * x.2 = t then a x.1 * β x.2 else 0

theorem blockCoeff_mul {Q : ℕ} {M : Finset ℕ} (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime Q) (a β : ℕ → ℝ)
    {x : ℕ × ℕ} (hx : x ∈ M ×ˢ Q.divisors) : blockCoeff Q M a β (x.1 * x.2) = a x.1 * β x.2 := by
  unfold blockCoeff
  rw [Finset.sum_eq_single x (fun y hy hyx => if_neg fun h =>
      hyx (mul_injOn_coprime_divisors hM hy hx h)) (fun h => absurd hx h), if_pos rfl]

/-- Sums over the block conductors are sums over pairs. -/
theorem sum_blockConductors {Q : ℕ} {M : Finset ℕ} (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime Q)
    {E : Type*} [AddCommMonoid E] (a β : ℕ → ℝ) (f : ℕ → ℝ → E) :
    ∑ t ∈ blockConductors Q M, f t (blockCoeff Q M a β t) =
      ∑ x ∈ M ×ˢ Q.divisors, f (x.1 * x.2) (a x.1 * β x.2) := by
  rw [blockConductors, Finset.sum_image (mul_injOn_coprime_divisors hM)]
  exact sum_congr rfl fun x hx => by rw [blockCoeff_mul hM a β hx]

theorem blockConductors_pos {Q : ℕ} {M : Finset ℕ}
    (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime Q) : ∀ t ∈ blockConductors Q M, 0 < t := by
  intro t ht
  obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
  obtain ⟨hm, hd⟩ := mem_product.mp hx
  exact Nat.mul_pos (hM _ hm).1 (Nat.pos_of_mem_divisors hd)

/-- **The block profile factors**: `Σ_t A_t e_t = (Σ_m a_m e_m) · (Σ_d β_d e_d)`. -/
theorem packetProfile_blockCoeff {Q : ℕ} {M : Finset ℕ} (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime Q)
    (a β : ℕ → ℝ) (n : ℕ) :
    packetProfile (blockConductors Q M) (blockCoeff Q M a β) n =
      packetProfile M a n * packetProfile Q.divisors β n := by
  unfold packetProfile
  rw [sum_blockConductors hM a β (fun t A => A * normalizedRamanujanMode t n), sum_mul_sum,
    ← Finset.sum_product']
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨hm, hd⟩ := mem_product.mp hx
  rw [normalizedRamanujanMode_mul_of_coprime (hM _ hm).1 (Nat.pos_of_mem_divisors hd)
    (Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd) (hM _ hm).2)]
  ring

end Blocks


/-! ### The flip energy of a block combination -/

section FlipEnergy

variable {S : Finset ℕ}

/-- Every flipped lag is prime to every conductor prime to `Q`. -/
theorem coprime_of_twistDefect_finiteFlip_ne_zero {k : ℕ}
    (hk : twistDefect (finiteFlipWeight S) k ≠ 0) {m : ℕ} (hm : m.Coprime (flipSetModulus S)) :
    k.Coprime m := by
  rw [twistDefect_finiteFlip] at hk
  have hΛ : vonMangoldtAtom k ≠ 0 := right_ne_zero_of_mul hk
  have h2 : 2 ≤ k := by
    by_contra h; exact hΛ (by simp [vonMangoldtAtom, h])
  have hΛk : (ArithmeticFunction.vonMangoldt k : ℝ) ≠ 0 := by
    intro h; exact hΛ (by simp [vonMangoldtAtom, h2, h])
  obtain ⟨q, j, hq, hj, rfl⟩ :=
    (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛk)
  have hqS : q ∈ S := by
    by_contra hqS
    rw [finiteFlip_prime_pow hq, if_neg hqS, sub_self, zero_mul] at hk
    exact hk rfl
  have hqQ : q ∣ flipSetModulus S := (dvd_pow_self q two_ne_zero).trans (sq_dvd_flipSetModulus hqS)
  exact Nat.Coprime.pow_left j (Nat.Coprime.coprime_dvd_left hqQ hm.symm)

/-- **The flip does not see the conductor.** For conductors `m` prime to `Q`, the flip energy of
`(Σ_m a_m e_m) · Y_S` is `Σ_m a_m²` times the flip energy of `Y_S`. -/
theorem twistLimitEnergy_block_combination (hS : ∀ p ∈ S, p.Prime) {M : Finset ℕ}
    (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime (flipSetModulus S)) (hMne : M.Nonempty) (a β : ℕ → ℝ)
    (hβ : packetProfile (flipSetModulus S).divisors β = flipSetTrial S) :
    twistLimitEnergy (finiteFlipWeight S)
        (packetProfile (blockConductors (flipSetModulus S) M)
          (blockCoeff (flipSetModulus S) M a β))
        (packetPeriod (blockConductors (flipSetModulus S) M)) =
      (∑ m ∈ M, a m ^ 2) *
        twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S) (flipSetModulus S) := by
  set Q := flipSetModulus S
  have hQ : 0 < Q := flipSetModulus_pos hS
  set T := blockConductors Q M
  have hT := blockConductors_pos hM
  set U := packetProfile M a
  have hMpos : ∀ m ∈ M, 0 < m := fun m hm => (hM m hm).1
  have hPU : 0 < packetPeriod M := packetPeriod_pos hMpos
  have hUper : Function.Periodic U (packetPeriod M) := packetProfile_periodic hMpos a
  have hYper : Function.Periodic (flipSetTrial S) Q := flipSetTrial_periodic (dvd_refl Q)
  have hcop : (packetPeriod M).Coprime Q := Nat.Coprime.prod_left fun m hm => (hM m hm).2
  -- the period of the block combination is a multiple of `P_M · Q`
  have hdvd : packetPeriod M * Q ∣ packetPeriod T := by
    obtain ⟨m₀, hm₀⟩ := hMne
    have hQT : m₀ * Q ∈ T := mem_image.mpr ⟨(m₀, Q), mem_product.mpr ⟨hm₀,
      Nat.mem_divisors_self _ hQ.ne'⟩, rfl⟩
    have h1 : Q ∣ packetPeriod T :=
      (dvd_mul_left Q m₀).trans (Finset.dvd_prod_of_mem _ hQT)
    have h2 : packetPeriod M ∣ packetPeriod T := by
      have hsub : M ⊆ T := fun m hm =>
        mem_image.mpr ⟨(m, 1), mem_product.mpr ⟨hm, Nat.one_mem_divisors.mpr hQ.ne'⟩, mul_one m⟩
      exact Finset.prod_dvd_prod_of_subset _ _ (fun t => t) hsub
    exact hcop.mul_dvd_of_dvd_of_dvd h2 h1
  obtain ⟨r, hr⟩ := hdvd
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · have := packetPeriod_pos hT; rw [hr, h, mul_zero] at this; exact absurd this (lt_irrefl 0)
    · exact h
  unfold twistLimitEnergy
  rw [show (∑ m ∈ M, a m ^ 2) * (2 * ∑' k, twistDefect (finiteFlipWeight S) k / Real.sqrt k *
      shiftMean (flipSetTrial S) Q k) = 2 * ∑' k, (∑ m ∈ M, a m ^ 2) *
        (twistDefect (finiteFlipWeight S) k / Real.sqrt k * shiftMean (flipSetTrial S) Q k) by
    rw [tsum_mul_left]; ring]
  congr 1
  refine tsum_congr fun k => ?_
  by_cases hk : twistDefect (finiteFlipWeight S) k = 0
  · simp [hk]
  have hkU : ∀ n, U (k * n) = U n := fun n => by
    unfold U packetProfile
    exact sum_congr rfl fun m hm => by
      rw [normalizedRamanujanMode_coprime_mul (hM m hm).1
        (coprime_of_twistDefect_finiteFlip_ne_zero hk (hM m hm).2)]
  have hprof : ∀ n, packetProfile T (blockCoeff Q M a β) n = U n * flipSetTrial S n := fun n => by
    rw [packetProfile_blockCoeff hM a β n, hβ]
  have hG : Function.Periodic (fun n => flipSetTrial S n * flipSetTrial S (k * n)) Q := by
    intro n
    simp only
    rw [hYper n, show k * (n + Q) = k * n + k * Q by ring]
    have := (hYper.nat_mul k) (k * n)
    simp only [Nat.cast_id] at this
    rw [this]
  have hU2 : Function.Periodic (fun n => U n ^ 2) (packetPeriod M) := fun n => by
    simp only; rw [hUper n]
  have hshift : shiftMean (packetProfile T (blockCoeff Q M a β)) (packetPeriod T) k =
      (∑ m ∈ M, a m ^ 2) * shiftMean (flipSetTrial S) Q k := by
    unfold shiftMean
    have hfun : (fun n => packetProfile T (blockCoeff Q M a β) n *
        packetProfile T (blockCoeff Q M a β) (k * n)) =
        fun n => U n ^ 2 * (flipSetTrial S n * flipSetTrial S (k * n)) := by
      funext n; rw [hprof, hprof, hkU]; ring
    have hU' : Function.Periodic (fun n => U n ^ 2) (packetPeriod M * Q) := by
      simpa only [Nat.cast_id, mul_comm] using hU2.nat_mul Q
    have hG' : Function.Periodic (fun n => flipSetTrial S n * flipSetTrial S (k * n))
        (packetPeriod M * Q) := by
      simpa only [Nat.cast_id] using hG.nat_mul (packetPeriod M)
    have hper : Function.Periodic (fun n => U n ^ 2 * (flipSetTrial S n * flipSetTrial S (k * n)))
        (packetPeriod M * Q) := fun n => by
      have h1 := hU' n
      have h2 := hG' n
      simp only at h1 h2 ⊢
      rw [h1, h2]
    rw [hfun, hr, mul_comm (packetPeriod M * Q) r, periodMean_mul_period (Nat.mul_pos hPU hQ) hper hr0,
      periodMean_mul_of_coprime hPU hQ hcop hU2 hG]
    congr 1
    have := periodMean_packet_mul hMpos (subset_refl M) (subset_refl M) a
    simp only [filter_true_of_mem (fun m (hm : m ∈ M) => hm)] at this
    rw [← this]
    congr 1
    funext n; rw [sq]
  rw [hshift]
  ring

/-- The **block energy** `b_m = Σ_{d∣Q} β_d² E_{md}(c) + τ_S` of the conductor-`m` block. -/
def blockEnergy (φ : ℝ → ℝ) (c : ℝ) (S : Finset ℕ) (β : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ (flipSetModulus S).divisors, β d ^ 2 * completedConductorEnergy φ c (m * d) +
    twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S) (flipSetModulus S)

/-- **Blocks are orthogonal.** The limiting twisted energy of `Σ_m a_m (e_m Y_S)` is
`Σ_m a_m² b_m`. -/
theorem packetEnergy_block_combination (hS : ∀ p ∈ S, p.Prime) {M : Finset ℕ}
    (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime (flipSetModulus S)) (hMne : M.Nonempty) (φ : ℝ → ℝ)
    (c : ℝ) (a β : ℕ → ℝ) (hβ : packetProfile (flipSetModulus S).divisors β = flipSetTrial S) :
    packetEnergy (finiteFlipWeight S) φ c (blockConductors (flipSetModulus S) M)
        (blockCoeff (flipSetModulus S) M a β) =
      ∑ m ∈ M, a m ^ 2 * blockEnergy φ c S β m := by
  unfold packetEnergy
  rw [twistLimitEnergy_block_combination hS hM hMne a β hβ,
    sum_blockConductors hM a β (fun t A => A ^ 2 * completedConductorEnergy φ c t),
    Finset.sum_product]
  unfold blockEnergy
  simp only [mul_add, sum_add_distrib, mul_sum, ← sum_mul]
  congr 1
  refine sum_congr rfl fun m _ => sum_congr rfl fun d _ => by ring

end FlipEnergy


/-! ### Negative definiteness on the blocks -/

section Negative

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- A quadratic form whose coefficients converge to a negative diagonal is eventually negative
definite. -/
theorem eventually_quadratic_neg (C : ℕ → K → K → ℝ) (e : K → ℝ) (he : ∀ k, e k < 0)
    (hC : ∀ k l, Tendsto (fun N => C N k l) atTop (𝓝 (if k = l then e k else 0))) :
    ∀ᶠ N : ℕ in atTop, ∀ a : K → ℝ, a ≠ 0 → ∑ k, ∑ l, a k * a l * C N k l < 0 := by
  rcases isEmpty_or_nonempty K with hK | hK
  · exact Eventually.of_forall fun N a ha => absurd (funext fun k => (IsEmpty.false k).elim) ha
  obtain ⟨k₀, hk₀⟩ := Finite.exists_max e
  set μ := -e k₀ with hμdef
  have hμ : 0 < μ := by linarith [he k₀]
  set ε := μ / (2 * ((Fintype.card K : ℝ) + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hev : ∀ᶠ N : ℕ in atTop, ∀ k l, |C N k l - (if k = l then e k else 0)| < ε :=
    eventually_all.mpr fun k => eventually_all.mpr fun l => by
      have h := (hC k l).sub_const (if k = l then e k else 0)
      rw [sub_self] at h
      exact (h.abs.eventually (gt_mem_nhds (by rw [abs_zero]; exact hε)))
  filter_upwards [hev] with N hN a ha
  have hS : 0 < ∑ k, a k ^ 2 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp ha
    exact lt_of_lt_of_le ((pow_pos (abs_pos.mpr hk) 2).trans_eq (sq_abs _))
      (single_le_sum (fun l _ => sq_nonneg (a l)) (mem_univ k))
  have hdiag : ∑ k, ∑ l, a k * a l * (if k = l then e k else 0) ≤ -μ * ∑ k, a k ^ 2 := by
    simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true, mul_sum]
    refine sum_le_sum fun k _ => ?_
    have := hk₀ k
    nlinarith [sq_nonneg (a k)]
  have herr : |∑ k, ∑ l, a k * a l * (C N k l - if k = l then e k else 0)| ≤
      ε * (∑ k, |a k|) ^ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_le_sum fun k _ => (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun l _ => ?_
    rw [abs_mul, abs_mul]
    nlinarith [(hN k l).le, abs_nonneg (a k), abs_nonneg (a l),
      mul_nonneg (abs_nonneg (a k)) (abs_nonneg (a l))]
  have hcs : (∑ k, |a k|) ^ 2 ≤ Fintype.card K * ∑ k, a k ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset K)) (f := fun k => |a k|)
    simpa [sq_abs] using this
  have hsplit : ∑ k, ∑ l, a k * a l * C N k l =
      ∑ k, ∑ l, a k * a l * (if k = l then e k else 0) +
        ∑ k, ∑ l, a k * a l * (C N k l - if k = l then e k else 0) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun l _ => by ring
  have h1 := (abs_le.mp herr).2
  have h2 : ε * (∑ k, |a k|) ^ 2 ≤ μ / 2 * ∑ k, a k ^ 2 := by
    calc ε * (∑ k, |a k|) ^ 2 ≤ ε * (Fintype.card K * ∑ k, a k ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hε.le
      _ = (Fintype.card K / (2 * ((Fintype.card K : ℝ) + 1))) * μ * ∑ k, a k ^ 2 := by
          rw [hεdef]; ring
      _ ≤ (1 / 2) * μ * ∑ k, a k ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hμ.le) hS.le
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
      _ = _ := by ring
  rw [hsplit]
  nlinarith

omit [DecidableEq K] in
/-- **Min–max.** A linear image of `ℝ^K` on which a symmetric matrix is negative definite forces at
least `#K` negative eigenvalues. -/
theorem card_le_negEigenvalues {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}
    (hA : A.IsHermitian) (syn : (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ I)
    (hneg : ∀ a, a ≠ 0 → ⟪Matrix.toEuclideanLin A (syn a), syn a⟫ < 0) :
    Fintype.card K ≤ (univ.filter fun i => hA.eigenvalues i < 0).card := by
  let J := univ.filter fun i => hA.eigenvalues i < 0
  let b := hA.eigenvectorBasis
  let L : (K → ℝ) →ₗ[ℝ] (J → ℝ) :=
    { toFun := fun a j => ⟪syn a, b j⟫
      map_add' := by intro a d; funext j; simp only [map_add, inner_add_left, Pi.add_apply]
      map_smul' := by
        intro r a; funext j
        simp only [map_smul, real_inner_smul_left, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    by_contra ha0
    have hlow : ∀ i, hA.eigenvalues i < 0 → ⟪syn a, b i⟫ = 0 := fun i hi =>
      congrFun (LinearMap.mem_ker.mp ha) ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have hge : 0 ≤ ⟪Matrix.toEuclideanLin A (syn a), syn a⟫ := by
      rw [HTGeometry.hermitianEnergy_eq_sum hA]
      refine sum_nonneg fun i _ => ?_
      by_cases hi : hA.eigenvalues i < 0
      · rw [hlow i hi]; simp
      · exact mul_nonneg (le_of_not_gt hi) (sq_nonneg _)
    exact absurd (hneg a ha0) (not_lt.mpr hge)
  have hdim := L.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hdim

end Negative

/-! ### Index growth of a flip set -/

section Growth

variable {φ : ℝ → ℝ} {S : Finset ℕ}

/-- The conductor-`m` block vector `Σ_{d∣Q} β_d r_{md}` at horizon `N`. -/
def blockVector (S : Finset ℕ) (β : ℕ → ℝ) (N m : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ d ∈ (flipSetModulus S).divisors, β d • normalizedRamanujanHorizonVector (m * d) N

theorem sum_blockVector_eq {M : Finset ℕ} (hM : ∀ m ∈ M, 0 < m ∧ m.Coprime (flipSetModulus S))
    (β : ℕ → ℝ) (N : ℕ) (a : M → ℝ) :
    ∑ i : M, a i • blockVector S β N i =
      ∑ t ∈ blockConductors (flipSetModulus S) M,
        blockCoeff (flipSetModulus S) M (subtypeCoeff M a) β t • normalizedRamanujanHorizonVector t N := by
  rw [sum_blockConductors hM (subtypeCoeff M a) β (fun t A => A • normalizedRamanujanHorizonVector t N),
    Finset.sum_product, sum_subtype_smul_eq M a (blockVector S β N)]
  refine sum_congr rfl fun m _ => ?_
  rw [blockVector, smul_sum]
  exact sum_congr rfl fun d _ => by rw [smul_smul]

/-- **Every low conductor sees the flip set.** If the blocks of a set `M` of conductors prime to
`Q` all have negative block energy at overlap `c`, the `S`-flipped complete Weil matrix eventually
has at least `#M` negative eigenvalues. -/
theorem eventually_flip_negative_eigenvalues (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    (hS : ∀ p ∈ S, p.Prime) {M : Finset ℕ} (hMc : ∀ m ∈ M, 0 < m ∧ m.Coprime (flipSetModulus S))
    {β : ℕ → ℝ} (hβ : packetProfile (flipSetModulus S).divisors β = flipSetTrial S)
    (hneg : ∀ m ∈ M, blockEnergy φ c S β m < 0) :
    ∀ᶠ N : ℕ in atTop, M.card ≤ (univ.filter fun i =>
      (twistedCompleteWeilMatrix_isHermitian (finiteFlipWeight S) φ c N).eigenvalues i < 0).card := by
  classical
  rcases M.eq_empty_or_nonempty with hMe | hMne
  · exact Eventually.of_forall fun N => by simp [hMe]
  set Q := flipSetModulus S
  have hQ : 0 < Q := flipSetModulus_pos hS
  have hT := blockConductors_pos hMc
  have hlam := summable_abs_twistDefect_finiteFlip hS
  set F : ℕ → (M → ℝ) → ℝ := fun N a =>
    ⟪Matrix.toEuclideanLin (twistedCompleteWeilMatrix (finiteFlipWeight S) φ c N)
      (∑ i : M, a i • blockVector S β N i), ∑ i : M, a i • blockVector S β N i⟫
  set C : ℕ → M → M → ℝ := fun N i j =>
    ⟪Matrix.toEuclideanLin (twistedCompleteWeilMatrix (finiteFlipWeight S) φ c N)
      (blockVector S β N i), blockVector S β N j⟫
  -- every coefficient vector has the diagonal limit
  have hF : ∀ a : M → ℝ, Tendsto (fun N => F N a) atTop
      (𝓝 (∑ i : M, a i ^ 2 * blockEnergy φ c S β i)) := by
    intro a
    have h := tendsto_twisted_packet hφ hsupp hM hc hlam hT (blockCoeff Q M (subtypeCoeff M a) β)
    rw [packetEnergy_block_combination hS hMc hMne φ c (subtypeCoeff M a) β hβ] at h
    have hval : ∑ m ∈ M, subtypeCoeff M a m ^ 2 * blockEnergy φ c S β m =
        ∑ i : M, a i ^ 2 * blockEnergy φ c S β i := by
      rw [← sum_coe_sort M]
      exact sum_congr rfl fun i _ => by simp only [subtypeCoeff, dif_pos i.property]
    rw [hval] at h
    refine h.congr fun N => ?_
    simp only [F]
    rw [sum_blockVector_eq hMc β N a]
  -- the form in coordinates
  have hFC : ∀ N a, F N a = ∑ i, ∑ j, a i * a j * C N i j := by
    intro N a
    simp only [F, C, map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hsingle : ∀ N (i : M), F N (Pi.single i 1) = C N i i := fun N i => by
    simp only [F, C, sum_single_smul]
  have hpair : ∀ N (i j : M), F N (Pi.single i 1 + Pi.single j 1) =
      C N i i + 2 * C N i j + C N j j := fun N i j => by
    have hs : ∑ k : M, (Pi.single i (1 : ℝ) + Pi.single j 1 : M → ℝ) k • blockVector S β N k =
        blockVector S β N i + blockVector S β N j := by
      simp only [Pi.add_apply, add_smul, sum_add_distrib, sum_single_smul]
    simp only [F, C]
    rw [hs, inner_add_self_eq (twistedCompleteWeilMatrix_isHermitian _ φ c N)]
  have hC : ∀ i j : M, Tendsto (fun N => C N i j) atTop
      (𝓝 (if i = j then blockEnergy φ c S β i else 0)) := by
    intro i j
    have hone : ∀ l : M, ∑ k : M, (Pi.single l (1 : ℝ) : M → ℝ) k ^ 2 * blockEnergy φ c S β k =
        blockEnergy φ c S β l := fun l => by
      rw [Finset.sum_eq_single l (fun k _ hk => by rw [Pi.single_eq_of_ne hk]; ring)
        (fun h => absurd (mem_univ l) h), Pi.single_eq_same]
      ring
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have h := hF (Pi.single i 1)
      rw [hone] at h
      exact h.congr fun N => hsingle N i
    · rw [if_neg hij]
      have h2 := hF (Pi.single i 1 + Pi.single j 1)
      have hi := hF (Pi.single i 1)
      have hj := hF (Pi.single j 1)
      rw [hone] at hi hj
      have htwo : ∑ k : M, (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ) : M → ℝ) k ^ 2 *
          blockEnergy φ c S β k = blockEnergy φ c S β i + blockEnergy φ c S β j := by
        rw [Finset.sum_eq_add i j hij (fun k _ hk => by
            rw [Pi.add_apply, Pi.single_eq_of_ne hk.1, Pi.single_eq_of_ne hk.2]; ring)
          (fun h => absurd (mem_univ i) h) (fun h => absurd (mem_univ j) h)]
        rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
          Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
        ring
      rw [htwo] at h2
      have hlim := ((h2.sub hi).sub hj).div_const 2
      rw [show (blockEnergy φ c S β i + blockEnergy φ c S β j - blockEnergy φ c S β i -
        blockEnergy φ c S β j) / 2 = 0 by ring] at hlim
      refine hlim.congr fun N => ?_
      rw [hpair, hsingle, hsingle]
      ring
  have hev := eventually_quadratic_neg C (fun i : M => blockEnergy φ c S β i)
    (fun i => hneg i i.property) hC
  filter_upwards [hev] with N hN
  let syn : (M → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    { toFun := fun a => ∑ i : M, a i • blockVector S β N i
      map_add' := by intro a d; simp only [Pi.add_apply, add_smul, sum_add_distrib]
      map_smul' := by
        intro r a; simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum, RingHom.id_apply] }
  have h := card_le_negEigenvalues (twistedCompleteWeilMatrix_isHermitian (finiteFlipWeight S) φ c N)
    syn fun a ha => by
      have := hN a ha
      rw [← hFC] at this
      exact this
  simpa only [Fintype.card_coe] using h

/-- **The index of a flip set grows without bound with the overlap.** For every nonempty finite set
of primes `S` and every `n` there is an overlap `c₀` such that at every `c ≥ c₀` the `S`-flipped
complete Weil matrix eventually has at least `n` negative eigenvalues. -/
theorem exists_overlap_flip_negIndex_ge (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) (n : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c, c₀ ≤ c → ∀ᶠ N : ℕ in atTop, n ≤ (univ.filter fun i =>
      (twistedCompleteWeilMatrix_isHermitian (finiteFlipWeight S) φ c N).eigenvalues i < 0).card := by
  classical
  set Q := flipSetModulus S
  have hQ : 0 < Q := flipSetModulus_pos hS
  obtain ⟨β, hβ⟩ := exists_flipSetTrial_packet hS
  -- `n` primes beyond `Q` are conductors prime to `Q`
  obtain ⟨M, hMsub, hMcard⟩ :=
    (Nat.infinite_setOf_prime.sdiff (Set.finite_Iic Q)).exists_subset_card_eq n
  have hMc : ∀ m ∈ M, 0 < m ∧ m.Coprime Q := by
    intro m hm
    have h := hMsub hm
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_Iic, not_le] at h
    refine ⟨h.1.pos, (Nat.Prime.coprime_iff_not_dvd h.1).mpr fun hdvd => ?_⟩
    exact absurd (Nat.le_of_dvd hQ hdvd) (not_le.mpr h.2)
  have hτ := twistLimitEnergy_finiteFlip_flipSetTrial_neg hS hne hQ (dvd_refl Q)
  -- each block energy tends to the negative flip energy of the product trial
  have hlim : ∀ m ∈ M, Tendsto (fun c => blockEnergy φ c S β m) atTop
      (𝓝 (twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S) Q)) := by
    intro m _
    have h := tendsto_finsetSum Q.divisors fun d _ =>
      (tendsto_completedConductorEnergy_atTop hφ hsupp hM (m * d)).const_mul (β d ^ 2)
    simp only [mul_zero, sum_const_zero] at h
    have h' := h.add_const (twistLimitEnergy (finiteFlipWeight S) (flipSetTrial S) Q)
    rw [zero_add] at h'
    exact h'
  have hev : ∀ᶠ c in atTop, ∀ m ∈ M, blockEnergy φ c S β m < 0 :=
    (eventually_all_finset M).mpr fun m hm => (hlim m hm).eventually (gt_mem_nhds hτ)
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp hev
  refine ⟨max c₁ 1, by positivity, fun c hc => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  have h := eventually_flip_negative_eigenvalues hφ hsupp hM hc0 hS hMc hβ
    (hc₁ c ((le_max_left _ _).trans hc))
  rw [hMcard] at h
  exact h

end Growth

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
