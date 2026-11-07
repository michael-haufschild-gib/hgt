import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHeckeActionOnProducers
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheStencilRateReachesVinogradovKorobov

/-!
# The parity balance of a producer

The twisted Dirichlet polynomial `D_{cλ}(s) = Σ c(k) λ(k) k^{-s}` has at `s = 1` the **parity balance**
`Σ c(k) λ(k)/k`. For a balanced stencil, with sawtooth weights `q_k = −c(k)/k`, it equals
`Σ q_k (1 − λ(k))`: twice the sawtooth mass on letters with `Ω` odd. A stencil is **parity neutral** when
this vanishes.

The factor of two of sieve parity appears here exactly. A Hecke factor `1 + j^{1−s}` with `λ(j) = −1`
neutralizes any producer and multiplies its normalized slope by exactly `2`, since the factor takes the
value `2` at `s = 1` and the parity twist `1 − j^{1−s}` vanishes there.

It is not a barrier. Mixing `c₁` with a dilated `c₂` gives the normalized slope
`A(c₁) + (x/y) slope(c₂) / (m₁ (1 − 1/B₁))`, where `x, y` are the two parity balances, so the factor `2`
is the case `x = y`. A Möbius producer has parity balance at least `2 m Σ_{P ≤ T} 1/P`, unbounded against
its slope `≈ m`. Taking `c₂` at a much larger level sends the cost to zero: **parity-neutral producers
exist at every rate above zero.** A linear parity constraint on the coefficients costs nothing in the
limit, so parity is not read by the balance of a stencil. A difference of adjacent dilates does better still,
and reaches the Mertens level.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

local notation "lam" => ArithmeticFunction.liouville

private lemma lam_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : lam (a * b) = lam a * lam b := by
  rw [ArithmeticFunction.liouville_apply (mul_ne_zero ha hb), ArithmeticFunction.liouville_apply ha,
    ArithmeticFunction.liouville_apply hb, ArithmeticFunction.cardFactors_mul ha hb, pow_add]

private lemma lam_eq_or {n : ℕ} (hn : n ≠ 0) : lam n = 1 ∨ lam n = -1 := by
  rw [ArithmeticFunction.liouville_apply hn]
  exact neg_one_pow_eq_or ℤ _

private lemma lam_prime {p : ℕ} (hp : p.Prime) : lam p = -1 := by
  rw [ArithmeticFunction.liouville_apply hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp,
    pow_one]

/-- The parity balance `Σ c(k) λ(k)/k`, the value of the Liouville twist at `s = 1`. -/
def parityBalance (c : ℕ →₀ ℤ) : ℝ := ∑ k ∈ c.support, (c k : ℝ) * (lam k : ℝ) / k

/-- The parity balance as a rational number. -/
def parityBalanceQ (c : ℕ →₀ ℤ) : ℚ := ∑ k ∈ c.support, (c k : ℚ) * (lam k : ℚ) / k

theorem cast_parityBalanceQ (c : ℕ →₀ ℤ) : ((parityBalanceQ c : ℚ) : ℝ) = parityBalance c := by
  rw [parityBalanceQ, parityBalance]
  push_cast
  rfl

private lemma parityBalance_eq_sum (c : ℕ →₀ ℤ) :
    parityBalance c = c.sum fun k a => (a : ℝ) * (lam k : ℝ) / k := rfl

theorem parityBalance_add (c d : ℕ →₀ ℤ) :
    parityBalance (c + d) = parityBalance c + parityBalance d := by
  simp only [parityBalance_eq_sum]
  exact Finsupp.sum_add_index' (by simp) (by intro _ a b; push_cast; ring)

theorem parityBalance_nsmul (c : ℕ →₀ ℤ) (a : ℕ) :
    parityBalance (a • c) = (a : ℝ) * parityBalance c := by
  induction a with
  | zero =>
    rw [zero_nsmul]
    simp [parityBalance]
  | succ a ih =>
    rw [succ_nsmul, parityBalance_add, ih]
    push_cast
    ring

/-- **The Hecke action on the parity balance.** The dilation by `j` multiplies it by `λ(j)/j`. -/
theorem parityBalance_dilate {j : ℕ} (hj : 0 < j) {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) :
    parityBalance (dilate j c) = (lam j : ℝ) / j * parityBalance c := by
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [parityBalance_eq_sum, dilate, Finsupp.sum_mapDomain_index (by simp) (by
    intro _ a b; push_cast; ring), parityBalance_eq_sum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k hk => ?_
  have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  rw [lam_mul hj.ne' hk0]
  push_cast
  field_simp

/-- **The parity balance is twice the mass on odd letters.** For a balanced stencil,
`Σ c(k) λ(k)/k = Σ q_k (1 − λ(k))` with `q_k = −c(k)/k`. -/
theorem parityBalance_eq_weights {c : ℕ →₀ ℤ} (hbal : IsBalanced c) :
    parityBalance c = ∑ k ∈ c.support, (-(c k : ℝ) / k) * (1 - (lam k : ℝ)) := by
  have h : ∑ k ∈ c.support, (c k : ℝ) / k = 0 := hbal
  have h' : parityBalance c = parityBalance c - ∑ k ∈ c.support, (c k : ℝ) / k := by rw [h, sub_zero]
  rw [h', parityBalance, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- **The factor of two.** A dilation by `j` with `λ(j) = −1` neutralizes any producer and exactly
doubles its normalized slope. -/
theorem IsProducer.parity_neutral_of_odd {c : ℕ →₀ ℤ} {m B j : ℕ} (hP : IsProducer c m B)
    (hj : 0 < j) (hlam : lam j = -1) :
    IsProducer (c + j • dilate j c) m B ∧ parityBalance (c + j • dilate j c) = 0 ∧
      normSlope (c + j • dilate j c) m B = 2 * normSlope c m B := by
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  refine ⟨hP.add_dilate hj j, ?_, ?_⟩
  · rw [parityBalance_add, parityBalance_nsmul, parityBalance_dilate hj hP.zero, hlam]
    push_cast
    field_simp
    ring
  · rw [hP.normSlope_add_dilate hj j, div_self hjR]
    ring

/-- **The mixing law.** Adding a dilated stencil adds the dilated slope to the normalized slope. -/
theorem IsProducer.normSlope_mix {c₁ c₂ : ℕ →₀ ℤ} {m₁ B₁ j N₁ N₂ : ℕ} (h₁ : IsProducer c₁ m₁ B₁)
    (hc₂0 : c₂ 0 = 0) (hc₂ : IsBalanced c₂) (hj : 0 < j) (hN₂ : 0 < N₂) :
    normSlope (N₂ • c₁ + N₁ • dilate j c₂) (N₂ * m₁) B₁ =
      normSlope c₁ m₁ B₁ + ((N₁ : ℝ) / N₂) * (stencilSlope c₂ / j) /
        ((m₁ : ℝ) * (1 - 1 / (B₁ : ℝ))) := by
  have hC := h₁.one_sub_pos
  have hm : (m₁ : ℝ) ≠ 0 := h₁.m_pos.ne'
  have hN : (N₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN₂.ne'
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [normSlope, normSlope, stencilSlope_add, stencilSlope_nsmul, stencilSlope_nsmul,
    stencilSlope_dilate hj hc₂0 hc₂]
  push_cast
  generalize (1 - 1 / (B₁ : ℝ)) = C at hC ⊢
  have hC' : C ≠ 0 := hC.ne'
  field_simp

/-- The prime harmonic sum up to `T`. -/
def primeHarmonic (T : ℕ) : ℝ := ∑ P ∈ primesUpTo T, 1 / (P : ℝ)

private lemma mem_primesUpTo_iff {T P : ℕ} : P ∈ primesUpTo T ↔ P.Prime ∧ P ≤ T := by
  simp only [primesUpTo, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.pos, h2⟩, h1⟩

theorem primeHarmonic_pos {T : ℕ} (hT : 2 ≤ T) : 0 < primeHarmonic T := by
  refine sum_pos' (fun P _ => by positivity) ⟨2, mem_primesUpTo_iff.mpr ⟨Nat.prime_two, hT⟩, ?_⟩
  norm_num

/-- The prime harmonic sum diverges. -/
theorem tendsto_primeHarmonic : Tendsto primeHarmonic atTop atTop := by
  set f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun _ _ => by positivity) n
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  refine (h.comp (tendsto_add_atTop_nat 1)).congr fun T => ?_
  have hsub : ∑ i ∈ range (T + 1), f i = ∑ i ∈ Icc 1 T, f i := by
    refine (sum_subset (fun i hi => ?_) (fun i hi hi' => ?_)).symm
    · have := mem_Icc.mp hi
      exact mem_range.mpr (by omega)
    · have hi0 : i = 0 := by
        by_contra h0
        exact hi' (mem_Icc.mpr ⟨Nat.pos_of_ne_zero h0, by have := mem_range.mp hi; omega⟩)
      subst hi0
      simp [hf, Nat.not_prime_zero]
  simp only [Function.comp]
  rw [hsub, primeHarmonic, primesUpTo, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  simp [hf, Set.indicator_apply]

private lemma two_le_of_mem_letters {T G k : ℕ} (hG : 2 ≤ G) (hk : k ∈ moebiusLetters T G) : 2 ≤ k := by
  rcases mem_union.mp hk with h | h
  · exact (mem_Icc.mp (mem_filter.mp h).1).1
  · obtain ⟨P, hP, rfl⟩ := mem_image.mp h
    exact hG.trans (Nat.le_mul_of_pos_right G (mem_primesUpTo_iff.mp hP).1.pos)

private lemma weight_mul_nonneg {T G k : ℕ} (hTG : T < G) (hk : k ∈ moebiusLetters T G) :
    0 ≤ (moebiusWeights T G k : ℝ) * (1 - (lam k : ℝ)) := by
  have hG2 : 2 ≤ G ∨ G = 1 := by omega
  have hk0 : k ≠ 0 := by
    rcases mem_union.mp hk with h | h
    · have := (mem_Icc.mp (mem_filter.mp h).1).1
      omega
    · obtain ⟨P, hP, rfl⟩ := mem_image.mp h
      exact Nat.mul_ne_zero (by omega) (mem_primesUpTo_iff.mp hP).1.ne_zero
  have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  by_cases hkT : k ≤ T
  · have hμ : ArithmeticFunction.moebius k = lam k := by
      have hsq : Squarefree k := by
        rcases mem_union.mp hk with h | h
        · exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (mem_filter.mp h).2
        · exfalso
          obtain ⟨P, hP, rfl⟩ := mem_image.mp h
          have hP1 := (mem_primesUpTo_iff.mp hP).1.pos
          have := Nat.le_mul_of_pos_right G hP1
          omega
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, ArithmeticFunction.liouville_apply hk0]
    rw [moebiusWeights, if_pos hkT, hμ]
    push_cast
    rcases lam_eq_or hk0 with h | h <;> rw [h] <;> push_cast <;> norm_num <;> positivity
  · rw [moebiusWeights, if_neg hkT]
    push_cast
    have h1 : (0 : ℝ) ≤ 1 - (lam k : ℝ) := by
      rcases lam_eq_or hk0 with h | h <;> rw [h] <;> norm_num
    positivity

/-- The parity balance of a Möbius stencil, read from its weights. -/
theorem IsMoebiusStencil.parityBalance_eq {c : ℕ →₀ ℤ} {m T G : ℕ} (h : IsMoebiusStencil c m T G)
    (hP : IsProducer c m G) :
    parityBalance c = (m : ℝ) * ∑ k ∈ moebiusLetters T G,
      (moebiusWeights T G k : ℝ) * (1 - (lam k : ℝ)) := by
  have hG2 := hP.two_le_B
  have h1 : 1 ∉ moebiusLetters T G := fun hmem => by
    have := two_le_of_mem_letters hG2 hmem
    omega
  rw [parityBalance_eq_weights hP.balanced,
    sum_subset h.support (fun k _ hk => by
      rw [Finsupp.notMem_support_iff.mp hk]
      simp),
    sum_insert h1, mul_sum]
  have hone : lam 1 = 1 := by
    rw [ArithmeticFunction.liouville_apply one_ne_zero]
    simp
  rw [hone]
  simp only [Int.cast_one, sub_self, mul_zero, zero_add]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℝ) ≠ 0 := by
    have := two_le_of_mem_letters hG2 hk
    exact Nat.cast_ne_zero.mpr (by omega)
  rw [h.letter k hk]
  field_simp

/-- **A Möbius producer is far from parity neutral.** Its parity balance is at least
`2 m Σ_{P ≤ T} 1/P`, while its slope is about `m`. -/
theorem IsMoebiusStencil.le_parityBalance {c : ℕ →₀ ℤ} {m T G : ℕ} (h : IsMoebiusStencil c m T G)
    (hP : IsProducer c m G) (hTG : T < G) :
    2 * (m : ℝ) * primeHarmonic T ≤ parityBalance c := by
  rw [h.parityBalance_eq hP]
  have hsub : primesUpTo T ⊆ moebiusLetters T G := fun P hP' => by
    obtain ⟨hpr, hle⟩ := mem_primesUpTo_iff.mp hP'
    refine mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hpr.two_le, hle⟩, ?_⟩)
    rw [ArithmeticFunction.moebius_apply_prime hpr]
    norm_num
  have hle := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun k => (moebiusWeights T G k : ℝ) * (1 - (lam k : ℝ)))
    (fun k hk _ => weight_mul_nonneg hTG hk)
  have hval : ∑ P ∈ primesUpTo T, (moebiusWeights T G P : ℝ) * (1 - (lam P : ℝ)) =
      2 * primeHarmonic T := by
    rw [primeHarmonic, mul_sum]
    refine sum_congr rfl fun P hP' => ?_
    obtain ⟨hpr, hle'⟩ := mem_primesUpTo_iff.mp hP'
    rw [moebiusWeights, if_pos hle', ArithmeticFunction.moebius_apply_prime hpr, lam_prime hpr]
    push_cast
    ring
  rw [hval] at hle
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc 2 * (m : ℝ) * primeHarmonic T = (m : ℝ) * (2 * primeHarmonic T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hm

/-- **The Möbius family has every rate.** For large `T` there is a Möbius producer at level `T` of
rate at most `η`. -/
theorem eventually_moebius_family {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∃ (c : ℕ →₀ ℤ) (m G : ℕ), T < G ∧ IsProducer c m G ∧
      IsMoebiusStencil c m T G ∧ rate c m G ≤ η := by
  have hβ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hlogT : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp1 := hlogT.eventually (HTGeometry.eventually_mul_rpow_le_exp_rpow (360 : ℝ)
    (c := 1 / 2) (δ := 1 / 2) (p := 2) hβ0 hβ0)
  have hp2 := hlogT.eventually
    ((tendsto_rpow_atTop hβ0).eventually_ge_atTop (-(2 * Real.log η)))
  filter_upwards [isMertensLevel_vk hβ0 (by norm_num), eventually_ge_atTop 2, hp1, hp2,
    hlogT.eventually_ge_atTop 1] with T hK hT2 h360 hv hu1
  obtain ⟨hδ0, hδ1, _, hM, hm, hsm⟩ := hK
  set u := Real.log (T : ℝ) with hu
  set v := u ^ ((1 : ℝ) / 2) with hvdef
  set δ := Real.exp (-v) with hδ
  have hT0 : (0 : ℝ) < T := by
    have : (2 : ℝ) ≤ T := by exact_mod_cast hT2
    linarith
  have hv0 : 0 ≤ v := by positivity
  have hvu : v ≤ u := by
    have := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num : (1 : ℝ) / 2 ≤ 1)
    rwa [Real.rpow_one] at this
  have hL2 : Real.log ((T : ℝ) ^ 2 / δ) = 2 * u + v := by
    rw [Real.log_div (by positivity) hδ0.ne', Real.log_pow, hδ, Real.log_exp]
    push_cast
    ring
  have hL3 : Real.log ((T : ℝ) ^ 3 / δ) = 3 * u + v := by
    rw [Real.log_div (by positivity) hδ0.ne', Real.log_pow, hδ, Real.log_exp]
    push_cast
    ring
  have hsmall : δ * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ)) ≤ 1 / 2 := by
    rw [hL2]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hδ0.le) hsm
    linarith
  obtain ⟨c, m, G, hGT, hP, _, hr, hst⟩ :=
    exists_moebius_producer_of_level_coeff hT2 hδ0 hδ1 hM hm hsmall
  refine ⟨c, m, G, hGT, hP, hst, hr.trans ?_⟩
  rw [hL2, hL3]
  have hδexp : Real.exp (v / 2) * δ = Real.exp (-(v / 2)) := by
    rw [hδ, ← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-(v / 2)) ≤ η := by
    rw [← Real.exp_log hη]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have h360' : 360 * u ^ 2 ≤ Real.exp (v / 2) := by
    have h := h360
    rw [Real.rpow_two] at h
    have heq : (1 : ℝ) / 2 * v = v / 2 := by ring
    rwa [heq] at h
  have hu0 : 0 ≤ u := by linarith
  have h1 : 3 + 2 * (2 * u + v) ≤ 9 * u := by linarith
  have h2 : 1 + (3 * u + v) ≤ 5 * u := by linarith
  have h3 : 0 ≤ 3 + 2 * (2 * u + v) := by positivity
  calc 8 * (δ * (3 + 2 * (2 * u + v))) * (1 + (3 * u + v))
      ≤ 8 * (δ * (9 * u)) * (5 * u) := by
        refine mul_le_mul ?_ h2 (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hδ0.le) (by norm_num)
    _ = (360 * u ^ 2) * δ := by ring
    _ ≤ Real.exp (v / 2) * δ := mul_le_mul_of_nonneg_right h360' hδ0.le
    _ = Real.exp (-(v / 2)) := hδexp
    _ ≤ η := hexp

private lemma mix_rate_le {x y S A H η ε : ℝ} (hx : 0 < x) (hA : 0 < A) (hH : 0 < H) (hy : 0 < y)
    (hη : 0 < η) (hS : 0 ≤ S) (hSy : S * H ≤ y) (hHbig : 2 * x / (A * η) ≤ H) (hε : ε ≤ η / 2) :
    ε + x / y * S / A ≤ η := by
  have h1 : S / y ≤ 1 / H := by
    rw [div_le_div_iff₀ hy hH]
    linarith
  have h2 : x / H ≤ A * η / 2 := by
    rw [div_le_iff₀ hH]
    have h3 := (div_le_iff₀ (by positivity : 0 < A * η)).mp hHbig
    linarith
  have h4 : x / y * S / A = (x * (S / y)) / A := by ring
  have h5 : (x * (S / y)) / A ≤ η / 2 := by
    rw [div_le_iff₀ hA]
    calc x * (S / y) ≤ x * (1 / H) := mul_le_mul_of_nonneg_left h1 hx.le
      _ = x / H := by ring
      _ ≤ A * η / 2 := h2
      _ = η / 2 * A := by ring
  rw [h4]
  linarith

/-- **Parity neutrality costs nothing in the limit.** For every `η > 0` there is an integer producer of
rate at most `η` and parity balance `0`. -/
theorem exists_parity_neutral_producer {η : ℝ} (hη : 0 < η) :
    ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ parityBalance c = 0 ∧ rate c m B ≤ η := by
  obtain ⟨T₁, ⟨c₁, m₁, G₁, hTG₁, h₁, hst₁, hr₁⟩, hT₁⟩ :=
    ((eventually_moebius_family (half_pos hη)).and (eventually_ge_atTop 2)).exists
  have hm₁ : (0 : ℝ) < m₁ := h₁.m_pos
  have hx : 0 < parityBalance c₁ :=
    lt_of_lt_of_le (by have := primeHarmonic_pos hT₁; positivity) (hst₁.le_parityBalance h₁ hTG₁)
  set A : ℝ := (m₁ : ℝ) * (1 - 1 / (G₁ : ℝ)) with hA
  have hA0 : 0 < A := mul_pos hm₁ h₁.one_sub_pos
  obtain ⟨T₂, ⟨c₂, m₂, G₂, hTG₂, h₂, hst₂, hr₂⟩, hT₂, hH⟩ :=
    ((eventually_moebius_family one_pos).and ((eventually_ge_atTop 2).and
      (tendsto_primeHarmonic.eventually_ge_atTop (2 * parityBalance c₁ / (A * η))))).exists
  have hH0 := primeHarmonic_pos hT₂
  have hm₂ : (0 : ℝ) < m₂ := h₂.m_pos
  have hyle := hst₂.le_parityBalance h₂ hTG₂
  have hy : 0 < parityBalance c₂ := lt_of_lt_of_le (by positivity) hyle
  -- The ratio of the two balances is rational.
  set r : ℚ := 2 * parityBalanceQ c₁ / parityBalanceQ c₂ with hr
  have hrR : (r : ℝ) = 2 * parityBalance c₁ / parityBalance c₂ := by
    rw [hr]
    push_cast
    rw [cast_parityBalanceQ, cast_parityBalanceQ]
  have hr0 : 0 < r := by
    have : (0 : ℝ) < r := by
      rw [hrR]
      positivity
    exact_mod_cast this
  set N₁ : ℕ := r.num.toNat with hN₁
  set N₂ : ℕ := r.den with hN₂
  have hN₂0 : 0 < N₂ := r.pos
  have hN₂R : (0 : ℝ) < N₂ := by exact_mod_cast hN₂0
  have hratio : (N₁ : ℝ) / N₂ = 2 * parityBalance c₁ / parityBalance c₂ := by
    rw [← hrR]
    have hnum : ((N₁ : ℤ) : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hr0).le
    have hcast : (N₁ : ℝ) = ((r.num : ℤ) : ℝ) := by exact_mod_cast hnum
    rw [hcast, hN₂, Rat.cast_def]
  have hj2 : (0 : ℕ) < 2 := by norm_num
  have hd0 : (N₁ • dilate 2 c₂) 0 = 0 := by simp [dilate_zero hj2 h₂.zero]
  have hP := (h₁.nsmul hN₂0).add_of_nonneg hd0
    (isBalanced_nsmul (isBalanced_dilate hj2 h₂.balanced) N₁)
    (stepWeight_nsmul_dilate_nonneg h₂.nonneg 2 N₁)
  refine ⟨N₂ • c₁ + N₁ • dilate 2 c₂, N₂ * m₁, G₁, hP, ?_, ?_⟩
  · rw [parityBalance_add, parityBalance_nsmul, parityBalance_nsmul,
      parityBalance_dilate hj2 h₂.zero, lam_prime Nat.prime_two]
    have hN : (N₁ : ℝ) = 2 * parityBalance c₁ / parityBalance c₂ * N₂ := by
      rw [← hratio]
      field_simp
    rw [hN]
    push_cast
    field_simp
    ring
  · rw [rate, h₁.normSlope_mix h₂.zero h₂.balanced hj2 hN₂0, hratio]
    have hS0 : 0 ≤ stencilSlope c₂ := h₂.slope_nonneg
    -- The helper has slope at most `2 m₂`.
    have hC₂ := h₂.one_sub_pos
    have hC₂1 : 1 - 1 / (G₂ : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / (G₂ : ℝ) := by positivity
      linarith
    have hnorm : normSlope c₂ m₂ G₂ ≤ 2 := by
      rw [rate] at hr₂
      linarith
    have hS : stencilSlope c₂ ≤ 2 * (m₂ : ℝ) := by
      have heq : stencilSlope c₂ = normSlope c₂ m₂ G₂ * ((m₂ : ℝ) * (1 - 1 / (G₂ : ℝ))) := by
        rw [normSlope, div_mul_cancel₀ _ (mul_pos hm₂ hC₂).ne']
      rw [heq]
      calc _ ≤ 2 * ((m₂ : ℝ) * (1 - 1 / (G₂ : ℝ))) :=
            mul_le_mul_of_nonneg_right hnorm (mul_pos hm₂ hC₂).le
        _ ≤ 2 * ((m₂ : ℝ) * 1) := by gcongr
        _ = _ := by ring
    have hSy : stencilSlope c₂ * primeHarmonic T₂ ≤ parityBalance c₂ := by
      refine le_trans ?_ hyle
      exact mul_le_mul_of_nonneg_right hS hH0.le
    have hmain := mix_rate_le (ε := rate c₁ m₁ G₁) hx hA0 hH0 hy hη hS0 hSy hH hr₁
    have hrewrite : normSlope c₁ m₁ G₁ + 2 * parityBalance c₁ / parityBalance c₂ *
        (stencilSlope c₂ / ((2 : ℕ) : ℝ)) / ((m₁ : ℝ) * (1 - 1 / (G₁ : ℝ))) - 1 =
        rate c₁ m₁ G₁ + parityBalance c₁ / parityBalance c₂ * stencilSlope c₂ / A := by
      rw [rate, hA]
      push_cast
      ring
    rw [hrewrite]
    exact hmain

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
