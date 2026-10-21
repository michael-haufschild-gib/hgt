import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiplicativeWeightsPretendingToOneArePaidOnlyByAVanishingLocalFactor
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FinitePerturbationsOfCoprimeWeightsAreDecidedAtThePole

/-!
# A vanishing finite local factor pays a weight pretending to one

Let `f` be multiplicative with `f(p) = 1` at every prime and `|f| ≤ B`, and let `p₀` be a prime at
which the local factor is finite (`f(p₀^k) = 0` for `k > K`) and vanishes at the pole:
`L_{p₀} = Σ_{k ≤ K} f(p₀^k) p₀^{-k} = 0`. Split `f = f₀ ⋆ f₁` into its `p₀`-part `f₀` (a finite kernel on
the powers of `p₀`) and its part `f₁ = 1_{(·,p₀)=1} f` prime to `p₀`; then `f₁ = h ⋆ 1_{(·,p₀)=1}` with
`h = 1_{(·,p₀)=1}(f ⋆ μ)` multiplicative and zero at every prime, hence critical Wiener. So

`f d^{-ε} = (h d^{-ε}) ⋆ (f₀ d^{-ε} ⋆ u_{p₀})`,

and the inner weight is a finite perturbation of the coprime weight `u_{p₀}` whose pole value is
exactly `L_{p₀} = 0`. Hence **the receiver of `f d^{-ε}` is bounded at every `ε > 0`.**

With the converse (no vanishing local factor ⇒ unbounded for `ε ≤ 1/2`): for multiplicative weights
pretending to one with finite local factors, **the receiver is paid if and only if some local factor
vanishes at the pole.** The arithmetic enters through the dilations `k ↦ p₀k` along a single prime.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "μR" => ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

/-! ### Arithmetic functions at a prime -/

/-- `(a ⋆ b)(p^k) = Σ_{i ≤ k} a(p^i) b(p^{k−i})`. -/
theorem mul_apply_prime_pow_eq (a b : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (a * b) (p ^ k) = ∑ i ∈ range (k + 1), a (p ^ i) * b (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => a x * b y),
    Nat.divisors_prime_pow hp, sum_map]
  refine sum_congr rfl fun i hi => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by have := mem_range.mp hi; omega) hp.pos]

/-- The indicator of the integers prime to `q`, as a completely multiplicative arithmetic function. -/
def coprimeAF (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else coprimeIndicator q n, by simp⟩

theorem coprimeAF_apply {q n : ℕ} (hn : n ≠ 0) : coprimeAF q n = coprimeIndicator q n := by
  simp [coprimeAF, hn]

theorem coprimeAF_mul (q a b : ℕ) : coprimeAF q (a * b) = coprimeAF q a * coprimeAF q b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [coprimeAF]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [coprimeAF]
  rw [coprimeAF_apply (mul_ne_zero ha hb), coprimeAF_apply ha, coprimeAF_apply hb]
  unfold coprimeIndicator
  simp only [Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

theorem pmul_coprimeAF_mul (q : ℕ) (f g : ArithmeticFunction ℝ) :
    (coprimeAF q).pmul (f * g) = (coprimeAF q).pmul f * (coprimeAF q).pmul g := by
  ext n
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.mul_apply, mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, coprimeAF_mul]; ring

theorem isMultiplicative_coprimeAF (q : ℕ) : (coprimeAF q).IsMultiplicative :=
  ⟨by simp [coprimeAF, coprimeIndicator], fun {_ _} _ => coprimeAF_mul q _ _⟩

/-- The `p`-part of `f` up to `p^K`: `f` on `{1, p, …, p^K}`, zero elsewhere. -/
def localPart (f : ArithmeticFunction ℝ) (p K : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∈ (range (K + 1)).image (fun i => p ^ i) then f n else 0, by simp⟩

theorem localPart_apply_pow (f : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (K i : ℕ) :
    localPart f p K (p ^ i) = if i ≤ K then f (p ^ i) else 0 := by
  simp only [localPart, ArithmeticFunction.coe_mk, mem_image, mem_range]
  congr 1
  apply propext
  constructor
  · rintro ⟨j, hj, hji⟩
    have := Nat.pow_right_injective hp.two_le hji
    omega
  · intro hi; exact ⟨i, by omega, rfl⟩

theorem localPart_apply_pow_of_ne (f : ArithmeticFunction ℝ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : q ≠ p) (K : ℕ) {i : ℕ} (hi : i ≠ 0) : localPart f p K (q ^ i) = 0 := by
  simp only [localPart, ArithmeticFunction.coe_mk, mem_image, mem_range]
  rw [if_neg]
  rintro ⟨j, -, hj⟩
  have hq' : q ∣ p ^ j := by rw [hj]; exact dvd_pow_self q hi
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq'))

theorem isMultiplicative_localPart {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) {p : ℕ}
    (hp : p.Prime) (K : ℕ) : (localPart f p K).IsMultiplicative := by
  set S := (range (K + 1)).image (fun i => p ^ i)
  have hmem : ∀ n, n ∈ S ↔ ∃ i ≤ K, n = p ^ i := fun n => by
    simp only [S, mem_image, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · simp only [localPart, ArithmeticFunction.coe_mk]
    rw [if_pos ((hmem 1).mpr ⟨0, Nat.zero_le _, by simp⟩), hf.map_one]
  simp only [localPart, ArithmeticFunction.coe_mk]
  by_cases hm : m ∈ S <;> by_cases hn : n ∈ S
  · obtain ⟨a, ha, rfl⟩ := (hmem m).mp hm
    obtain ⟨b, hb, rfl⟩ := (hmem n).mp hn
    have hab : a = 0 ∨ b = 0 := by
      by_contra h
      push Not at h
      have h1 : p ∣ Nat.gcd (p ^ a) (p ^ b) :=
        Nat.dvd_gcd (dvd_pow_self p h.1) (dvd_pow_self p h.2)
      rw [hmn] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    have hmnS : p ^ a * p ^ b ∈ S := by
      rcases hab with rfl | rfl
      · simpa using (hmem _).mpr ⟨b, hb, rfl⟩
      · simpa using (hmem _).mpr ⟨a, ha, rfl⟩
    rw [if_pos hmnS, if_pos hm, if_pos hn, hf.map_mul_of_coprime hmn]
  all_goals
    have hnot : m * n ∉ S := by
      intro hmnS
      obtain ⟨c, hc, hcmn⟩ := (hmem _).mp hmnS
      have hmd : m ∣ p ^ c := hcmn ▸ dvd_mul_right m n
      have hnd : n ∣ p ^ c := hcmn ▸ dvd_mul_left n m
      obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow hp).mp hmd
      obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hp).mp hnd
      first
        | exact hm ((hmem _).mpr ⟨a, by omega, rfl⟩)
        | exact hn ((hmem _).mpr ⟨b, by omega, rfl⟩)
    rw [if_neg hnot]
  · rw [if_neg hn, mul_zero]
  · rw [if_neg hm, zero_mul]
  · rw [if_neg hm, zero_mul]

/-! ### The decomposition -/

section Decomposition

variable {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) {p₀ : ℕ} (hp₀ : p₀.Prime) {K : ℕ}
  (hfin : ∀ k, K < k → f (p₀ ^ k) = 0)
include hf hp₀ hfin

/-- **`f = f₀ ⋆ (1_{(·,p₀)=1} f)`**: a multiplicative function splits at one prime. -/
theorem localPart_mul_pmul_coprime :
    localPart f p₀ K * (coprimeAF p₀).pmul f = f := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_localPart hf hp₀ K).mul ((isMultiplicative_coprimeAF p₀).pmul hf)) _ hf).mpr
    fun p k hp => ?_
  rw [mul_apply_prime_pow_eq _ _ hp]
  by_cases hpp : p = p₀
  · subst hpp
    rw [sum_eq_single k (fun i hi hik => ?_) (fun h => absurd (self_mem_range_succ k) h), Nat.sub_self,
      pow_zero, ArithmeticFunction.pmul_apply, (isMultiplicative_coprimeAF p).map_one,
      hf.map_one, mul_one, mul_one, localPart_apply_pow f hp]
    · split_ifs with hk
      · rfl
      · exact (hfin k (by omega)).symm
    · have hki : k - i ≠ 0 := by have := mem_range.mp hi; omega
      rw [ArithmeticFunction.pmul_apply, coprimeAF_apply (pow_ne_zero _ hp.ne_zero)]
      unfold coprimeIndicator
      rw [if_neg (by
        rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hki)]
        exact fun h => (hp.coprime_iff_not_dvd.mp h) dvd_rfl), zero_mul, mul_zero]
  · rw [sum_eq_single 0 (fun i hi hi0 => ?_) (fun h => absurd (mem_range.mpr (Nat.succ_pos k)) h),
      pow_zero, (isMultiplicative_localPart hf hp₀ K).map_one, one_mul, Nat.sub_zero,
      ArithmeticFunction.pmul_apply]
    · rcases eq_or_ne k 0 with rfl | hk
      · simp [(isMultiplicative_coprimeAF p₀).map_one]
      rw [coprimeAF_apply (pow_ne_zero _ hp.ne_zero)]
      unfold coprimeIndicator
      rw [if_pos (Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hp₀).mpr hpp)), one_mul]
    · rw [localPart_apply_pow_of_ne f hp₀ hp hpp K hi0, zero_mul]

end Decomposition

/-! ### The receiver -/

/-- **A vanishing finite local factor pays a weight pretending to one.** If `f` is multiplicative,
`f(p) = 1` at every prime, `|f| ≤ B`, and at a prime `p₀` the local factor is finite
(`f(p₀^k) = 0` for `k > K`) and vanishes at the pole, `Σ_k f(p₀^k) p₀^{-k} = 0`, then the receiver of
`f(d) d^{-ε}` is bounded for every `ε > 0`. -/
theorem receiverBounded_of_poleLocalFactor_eq_zero {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = 1) {B : ℝ} (hB : ∀ n, |f n| ≤ B)
    {p₀ : ℕ} (hp₀ : p₀.Prime) {K : ℕ} (hfin : ∀ k, K < k → f (p₀ ^ k) = 0)
    (hL : poleLocalFactor f p₀ = 0) {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded (dampedSignWeight ⇑f ε) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  set χ := coprimeAF p₀
  set g := f * μR
  have hg : g.IsMultiplicative := hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast
  set h := χ.pmul g
  have hh : h.IsMultiplicative := (isMultiplicative_coprimeAF p₀).pmul hg
  have hhp : ∀ p : ℕ, p.Prime → h p = 0 := fun p hp => by
    simp only [h, ArithmeticFunction.pmul_apply]
    by_cases hpp : p = p₀
    · subst hpp
      rw [coprimeAF_apply hp.ne_zero]
      simp [coprimeIndicator, Nat.coprime_self, hp.one_lt.ne']
    · have := mul_moebius_apply_prime_pow f hp 0
      rw [zero_add, pow_one, pow_zero, hf.map_one, hfp p hp, sub_self] at this
      simp only [g, this, mul_zero]
  have hhk : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 2 ≤ k → |h (p ^ k)| ≤ (2 * B + 1) * k := fun p hp k hk => by
    simp only [h, ArithmeticFunction.pmul_apply]
    have hχ : |χ (p ^ k)| ≤ 1 := by
      rcases eq_or_ne (p ^ k) 0 with h0 | h0
      · simp [h0]
      · rw [coprimeAF_apply h0]; unfold coprimeIndicator; split_ifs <;> norm_num
    rw [abs_mul]
    calc |χ (p ^ k)| * |g (p ^ k)| ≤ 1 * (2 * B + 1) :=
          mul_le_mul hχ (abs_mul_moebius_apply_le hf hB hp k) (abs_nonneg _) zero_le_one
      _ ≤ (2 * B + 1) * k := by
          rw [one_mul]; exact le_mul_of_one_le_right (by linarith) (by exact_mod_cast (by omega : 1 ≤ k))
  have hW := criticalWiener_of_multiplicative hh hhp (by linarith) hhk hε
  -- `1_{(·,p₀)=1} f = h ⋆ 1_{(·,p₀)=1}`
  have hf₁ : χ.pmul f = h * χ := by
    have hz : χ.pmul ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) = χ := by
      ext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp
    have hfg : f = g * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
      simp only [g]; rw [mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
    conv_lhs => rw [hfg]
    rw [pmul_coprimeAF_mul, hz]
  -- `f = f₀ ⋆ h ⋆ χ`
  set f₀ := localPart f p₀ K
  have hsplit : f = h * (f₀ * χ) := by
    rw [← localPart_mul_pmul_coprime hf hp₀ hfin, hf₁]; ring
  -- the inner weight is a finite perturbation of the coprime weight
  have hf₀J : ∀ j, p₀ ^ K < j → dampedSignWeight ⇑f₀ ε j = 0 := fun j hj => by
    simp only [dampedSignWeight, f₀, localPart, ArithmeticFunction.coe_mk, mem_image, mem_range]
    rw [if_neg, zero_mul]
    rintro ⟨i, hi, rfl⟩
    exact absurd hj (not_lt.mpr (Nat.pow_le_pow_right hp₀.pos (by omega)))
  have hpole : poleValue (dampedSignWeight ⇑f₀ ε) (p₀ ^ K) ε = 0 := by
    have hcell : ∀ j ∈ Icc 1 (p₀ ^ K), dampedSignWeight ⇑f₀ ε j * (j : ℝ) ^ (-(1 - ε)) = f₀ j / j :=
      fun j hj => by
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [dampedSignWeight, mul_assoc, ← Real.rpow_add hj0, show -ε + -(1 - ε) = -1 by ring,
          Real.rpow_neg_one, div_eq_mul_inv]
    rw [poleValue, sum_congr rfl hcell]
    -- only the powers of `p₀` contribute
    have hsub : (range (K + 1)).image (fun i => p₀ ^ i) ⊆ Icc 1 (p₀ ^ K) := fun n hn => by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
      exact mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp₀.pos,
        Nat.pow_le_pow_right hp₀.pos (by have := mem_range.mp hi; omega)⟩
    rw [← sum_subset hsub fun n _ hn => by
      simp only [f₀, localPart, ArithmeticFunction.coe_mk, if_neg hn, zero_div]]
    rw [sum_image fun a _ b _ hab => Nat.pow_right_injective hp₀.two_le hab]
    have hterm : ∀ i ∈ range (K + 1), f₀ (p₀ ^ i) / ((p₀ ^ i : ℕ) : ℝ) =
        f (p₀ ^ i) * ((p₀ : ℝ)⁻¹) ^ i := fun i hi => by
      rw [localPart_apply_pow f hp₀, if_pos (by have := mem_range.mp hi; omega)]
      push_cast; rw [inv_pow, div_eq_mul_inv]
    rw [sum_congr rfl hterm, ← hL, poleLocalFactor, tsum_eq_sum (s := range (K + 1)) fun i hi => by
      rw [hfin i (by have := mem_range.mpr.mt hi; omega), zero_mul]]
  set k := dampedSignWeight ⇑f₀ ε
  set L := ∑ j ∈ Icc 1 (p₀ ^ K), |undampedKernel k ε j|
  have hL : 0 ≤ L := sum_nonneg fun j _ => abs_nonneg _
  have hinnerEq : RHTower.dirichletConv k (dampedSignWeight (coprimeIndicator p₀) ε) =
      dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) (coprimeIndicator p₀)) ε :=
    funext (dirichletConv_damped_eq k (coprimeIndicator p₀) ε)
  have hinner : ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight (coprimeIndicator p₀) ε)) := by
    rw [hinnerEq]
    exact exists_weightPronicEnergy_dampedSign_le (mul_nonneg (by positivity) hL) hε
      (abs_sum_range_dirichletConv_coprime_le hp₀.pos hf₀J hpole)
  have hsign : ∀ d, |RHTower.dirichletConv (undampedKernel k ε) (coprimeIndicator p₀) d| ≤ L :=
    fun d => by
    unfold RHTower.dirichletConv
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ d.divisors, |undampedKernel k ε j * coprimeIndicator p₀ (d / j)| ≤
          ∑ j ∈ d.divisors.filter (· ≤ p₀ ^ K), |undampedKernel k ε j| := by
          rw [sum_filter]
          refine sum_le_sum fun j _ => ?_
          split_ifs with hj
          · rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (by
              rw [abs_of_nonneg (coprimeIndicator_nonneg _ _)]; exact coprimeIndicator_le_one _ _)
          · rw [undampedKernel_support hf₀J ε j (by omega), zero_mul, abs_zero]
      _ ≤ L := sum_le_sum_of_subset_of_nonneg (fun j hj => by
            obtain ⟨hjd, hjJ⟩ := mem_filter.mp hj
            exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hjd, hjJ⟩) fun _ _ _ => abs_nonneg _
  have hs : Summable (fun d : ℕ =>
      |RHTower.dirichletConv k (dampedSignWeight (coprimeIndicator p₀) ε) d / d|) := by
    rw [hinnerEq]
    refine ((Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).mul_left L).of_nonneg_of_le
      (fun _ => abs_nonneg _) fun d => ?_
    rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hsign d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hχ : dampedSignWeight ⇑χ ε = dampedSignWeight (coprimeIndicator p₀) ε := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [dampedSignWeight, Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
    · rw [dampedSignWeight, dampedSignWeight, coprimeAF_apply hn]
  have hfun : dampedSignWeight ⇑f ε = RHTower.dirichletConv (dampedSignWeight ⇑h ε)
      (RHTower.dirichletConv k (dampedSignWeight (coprimeIndicator p₀) ε)) := by
    funext n
    have hdamp : ∀ (a b : ArithmeticFunction ℝ) (m : ℕ), dampedSignWeight ⇑(a * b) ε m =
        RHTower.dirichletConv (dampedSignWeight ⇑a ε) (dampedSignWeight ⇑b ε) m := fun a b m => by
      rw [← dampedSignWeight_dirichletConv]
      simp only [dampedSignWeight, mul_apply_eq_dirichletConv]
    have hinnerfun : dampedSignWeight ⇑(f₀ * χ) ε =
        RHTower.dirichletConv k (dampedSignWeight (coprimeIndicator p₀) ε) := by
      funext m; rw [hdamp, hχ]
    conv_lhs => rw [hsplit]
    rw [hdamp, hinnerfun]
  rw [hfun]
  exact receiverBounded_dirichletConv hW hs hinner

/-- **Weights pretending to one with finite local factors are paid exactly by a vanishing local
factor.** If `f` is multiplicative, `f(p) = 1` at every prime, `|f| ≤ B`, and every local factor is
finite (`f(p^k) = 0` for `k > K`), then for `0 < ε ≤ 1/2` the receiver of `f(d) d^{-ε}` is bounded if
and only if `Σ_k f(p^k) p^{-k} = 0` at some prime `p`. -/
theorem receiverBounded_iff_exists_poleLocalFactor_eq_zero {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = 1) {B : ℝ} (hB : ∀ n, |f n| ≤ B)
    {K : ℕ} (hfin : ∀ p : ℕ, p.Prime → ∀ k, K < k → f (p ^ k) = 0) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ReceiverBounded (dampedSignWeight ⇑f ε) ↔ ∃ p : ℕ, p.Prime ∧ poleLocalFactor f p = 0 := by
  constructor
  · intro hR
    by_contra hall
    push Not at hall
    exact not_receiverBounded_of_primes_one_of_poleLocalFactor_ne_zero hf hfp hB hε hε2 hall hR
  · rintro ⟨p, hp, hL⟩
    exact receiverBounded_of_poleLocalFactor_eq_zero hf hfp hB hp (hfin p hp) hL hε

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
