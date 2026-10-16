import GaloisForLFunctions.RHTower.LeeYangPrimePivotDualSpectrum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Nat.Log

/-!
# Spin partition, exact frequency spectrum and wall budget of Γ-site chains at a prime pivot

The Γ-site chain on sites `0, …, N` has fields `u_i = e^{-i t log((i+2)/(i+1))}` and wall
fugacities `c_k` between sites `k` and `k+1`.

* `chainZ_eq_spinSum`: the transfer recursion `chainPair` is the spin sum
  `Z = Σ_{S ⊆ {0..N}} (∏_{walls k of S} c_k) ∏_{i ∈ S} u_i`.
* `gammaChainZ_eq_frequencySum`: grouping spin words by their frequency
  `log q(S)`, `q(S) = ∏_{i∈S} (i+2)/(i+1)`, writes `Z` as a finite exponential sum.
* `gammaChain_expSum_coeff_eq`: exponentials with distinct real frequencies are linearly
  independent (Dedekind), so the coefficients of any exponential-sum representation of `Z` are the
  fiber sums of the spin weights.  With nonnegative fugacities there is no cancellation
  (`gammaChain_spectrum_iff`): the frequencies with nonzero coefficient are exactly the `log q(S)`
  of the spin words whose walls all have positive fugacity.
* `primePivot_spinSpectrum_dual_iff_divisibility_chain`: at a prime pivot `M = N + 2`, all such
  words lie in the dual alphabet `ℕ ∪ M/ℕ` iff the active walls `n = k + 2` form an ordered
  divisibility chain.  The converse direction uses the block decomposition of a spin word.
* `two_pow_card_lt_of_divisibility_chain`, `exists_divisibility_chain_card_eq_log`: a chain has
  `2 ^ r ≤ N + 1 < M` active walls, and powers of two attain `r = ⌊log₂ (M - 1)⌋`.
* `gammaChainCoeffPoly_coeff_twoWall`: for independent signed fugacities, the coefficient of the
  two-wall frequency `log ((k+2)/(j+2))` is a polynomial whose `c_j c_k` coefficient is one, so it
  is a nonzero polynomial.
-/

open Finset Complex

namespace RHTower.LeeYangChain

noncomputable section

/-! ### Walls and fugacity weights -/

instance gammaSpinWallAtDecidable (S : Finset ℕ) : DecidablePred (GammaSpinWallAt S) :=
  fun i => by unfold GammaSpinWallAt; infer_instance

/-- Walls of a spin word strictly below site `k`. -/
def gammaSpinWalls (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (range k).filter (GammaSpinWallAt S)

theorem mem_gammaSpinWalls {k : ℕ} {S : Finset ℕ} {i : ℕ} :
    i ∈ gammaSpinWalls k S ↔ i < k ∧ GammaSpinWallAt S i := by
  simp [gammaSpinWalls]

/-- Fugacity weight `∏_{walls k} c_k` of a spin word on sites `0..N`. -/
def gammaSpinWeight (c : ℕ → ℝ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∏ i ∈ gammaSpinWalls N S, c i

theorem gammaSpinWeight_succ_of_wall (c : ℕ → ℝ) {k : ℕ} {S : Finset ℕ}
    (hw : GammaSpinWallAt S k) :
    gammaSpinWeight c (k + 1) S = c k * gammaSpinWeight c k S := by
  unfold gammaSpinWeight gammaSpinWalls
  rw [range_succ, filter_insert, if_pos hw, prod_insert (by simp)]

theorem gammaSpinWeight_succ_of_not_wall (c : ℕ → ℝ) {k : ℕ} {S : Finset ℕ}
    (hw : ¬GammaSpinWallAt S k) :
    gammaSpinWeight c (k + 1) S = gammaSpinWeight c k S := by
  unfold gammaSpinWeight gammaSpinWalls
  rw [range_succ, filter_insert, if_neg hw]

theorem gammaSpinWalls_insert_succ (k : ℕ) (S : Finset ℕ) :
    gammaSpinWalls k (insert (k + 1) S) = gammaSpinWalls k S := by
  ext i
  simp only [mem_gammaSpinWalls, GammaSpinWallAt, mem_insert]
  constructor <;> rintro ⟨hi, hw⟩ <;> refine ⟨hi, ?_⟩ <;> omega

/-! ### The spin expansion of the transfer recursion -/

/-- The transfer weights `(A_k, B_k)` are spin sums over the words on sites `0..k` whose last
spin is `+`, resp. `−`. -/
theorem chainPair_eq_spinSum (c : ℕ → ℝ) (u : ℕ → ℂ) (k : ℕ) :
    (chainPair c u k).1 = ∑ S ∈ (range (k + 1)).powerset,
        (if k ∈ S then 0 else (gammaSpinWeight c k S : ℂ) * ∏ i ∈ S, u i) ∧
    (chainPair c u k).2 = ∑ S ∈ (range (k + 1)).powerset,
        (if k ∈ S then (gammaSpinWeight c k S : ℂ) * ∏ i ∈ S, u i else 0) := by
  induction k with
  | zero =>
    simp [chainPair, gammaSpinWeight, gammaSpinWalls, range_one, powerset_singleton]
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    have hk : k + 1 ∉ range (k + 1) := by simp
    have hsub (t : Finset ℕ) (ht : t ∈ (range (k + 1)).powerset) : k + 1 ∉ t := by
      intro h
      have := mem_range.mp (mem_powerset.mp ht h)
      omega
    have hwall (t : Finset ℕ) (ht : t ∈ (range (k + 1)).powerset) :
        GammaSpinWallAt t k ↔ k ∈ t := by
      have := hsub t ht
      unfold GammaSpinWallAt
      tauto
    have hwall' (t : Finset ℕ) (ht : t ∈ (range (k + 1)).powerset) :
        GammaSpinWallAt (insert (k + 1) t) k ↔ k ∉ t := by
      unfold GammaSpinWallAt
      simp only [mem_insert, self_eq_add_right, one_ne_zero, false_or, true_or, not_true_eq_false,
        and_false, and_true, or_false]
      constructor
      · rintro h
        exact h
      · intro h
        exact h
    have hweight (t : Finset ℕ) (ht : t ∈ (range (k + 1)).powerset) :
        gammaSpinWeight c (k + 1) t =
          if k ∈ t then c k * gammaSpinWeight c k t else gammaSpinWeight c k t := by
      split_ifs with hkt
      · exact gammaSpinWeight_succ_of_wall c ((hwall t ht).mpr hkt)
      · exact gammaSpinWeight_succ_of_not_wall c (fun h => hkt ((hwall t ht).mp h))
    have hweight' (t : Finset ℕ) (ht : t ∈ (range (k + 1)).powerset) :
        gammaSpinWeight c (k + 1) (insert (k + 1) t) =
          if k ∈ t then gammaSpinWeight c k t else c k * gammaSpinWeight c k t := by
      split_ifs with hkt
      · rw [gammaSpinWeight_succ_of_not_wall c (fun h => (hwall' t ht).mp h hkt)]
        unfold gammaSpinWeight
        rw [gammaSpinWalls_insert_succ]
      · rw [gammaSpinWeight_succ_of_wall c ((hwall' t ht).mpr hkt)]
        unfold gammaSpinWeight
        rw [gammaSpinWalls_insert_succ]
    rw [range_succ (k + 1), sum_powerset_insert hk, sum_powerset_insert hk]
    constructor
    · have h2 : ∑ t ∈ (range (k + 1)).powerset,
          (if k + 1 ∈ insert (k + 1) t then (0 : ℂ) else
            (gammaSpinWeight c (k + 1) (insert (k + 1) t) : ℂ) *
              ∏ i ∈ insert (k + 1) t, u i) = 0 := by simp
      rw [h2, add_zero]
      change (chainPair c u k).1 + (c k : ℂ) * (chainPair c u k).2 = _
      rw [hA, hB, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun t ht => ?_
      rw [if_neg (hsub t ht), hweight t ht]
      split_ifs <;> push_cast <;> ring
    · have h1 : ∑ t ∈ (range (k + 1)).powerset,
          (if k + 1 ∈ t then (gammaSpinWeight c (k + 1) t : ℂ) * ∏ i ∈ t, u i else 0) = 0 :=
        sum_eq_zero fun t ht => if_neg (hsub t ht)
      rw [h1, zero_add]
      change u (k + 1) * ((c k : ℂ) * (chainPair c u k).1 + (chainPair c u k).2) = _
      rw [hA, hB, mul_sum, ← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun t ht => ?_
      rw [if_pos (mem_insert_self _ _), hweight' t ht, prod_insert (hsub t ht)]
      split_ifs <;> push_cast <;> ring

/-- The partition function is the spin sum `Σ_S (∏_{walls} c_k) ∏_{i ∈ S} u_i`. -/
theorem chainZ_eq_spinSum (c : ℕ → ℝ) (u : ℕ → ℂ) (N : ℕ) :
    chainZ c u N = ∑ S ∈ (range (N + 1)).powerset, (gammaSpinWeight c N S : ℂ) * ∏ i ∈ S, u i := by
  obtain ⟨hA, hB⟩ := chainPair_eq_spinSum c u N
  rw [chainZ, hA, hB, ← sum_add_distrib]
  refine sum_congr rfl fun S _ => ?_
  split_ifs <;> simp

/-! ### Frequencies of spin words -/

/-- The real frequency `log q(S)` of a spin word. -/
def gammaSpinFrequency (S : Finset ℕ) : ℝ := Real.log (gammaSpinWordRatio S : ℝ)

theorem gammaSiteRatio_cast (i : ℕ) :
    ((gammaSiteRatio i : ℚ) : ℝ) = ((i : ℝ) + 2) / ((i : ℝ) + 1) := by
  simp [gammaSiteRatio]

theorem gammaSpinWordRatio_pos (S : Finset ℕ) : 0 < gammaSpinWordRatio S :=
  prod_pos fun i _ => by unfold gammaSiteRatio; positivity

theorem sum_gammaFreq_eq_gammaSpinFrequency (S : Finset ℕ) :
    ∑ i ∈ S, gammaFreq i = gammaSpinFrequency S := by
  unfold gammaSpinFrequency gammaSpinWordRatio
  rw [Rat.cast_prod, Real.log_prod (fun i _ => by rw [gammaSiteRatio_cast]; positivity)]
  refine sum_congr rfl fun i _ => ?_
  rw [gammaSiteRatio_cast, gammaFreq]

theorem prod_gammaSiteField_eq (t : ℝ) (S : Finset ℕ) :
    ∏ i ∈ S, chainExpField gammaFreq (t : ℂ) i =
      cexp (-(I * (gammaSpinFrequency S : ℂ) * t)) := by
  rw [prod_chainExpField, sum_gammaFreq_eq_gammaSpinFrequency]

/-- The finite set of frequencies of the spin words on sites `0..N`. -/
def gammaChainFrequencies (N : ℕ) : Finset ℝ :=
  (range (N + 1)).powerset.image gammaSpinFrequency

/-- The coefficient at frequency `λ`: the total weight of the spin words with that frequency. -/
def gammaChainCoeff (c : ℕ → ℝ) (N : ℕ) (lam : ℝ) : ℝ :=
  ∑ S ∈ (range (N + 1)).powerset.filter (fun S => gammaSpinFrequency S = lam),
    gammaSpinWeight c N S

/-- The Γ-site chain is the finite exponential sum `Σ_λ C_λ e^{-iλt}` over spin-word frequencies. -/
theorem gammaChainZ_eq_frequencySum (c : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    chainZ c (chainExpField gammaFreq (t : ℂ)) N =
      ∑ lam ∈ gammaChainFrequencies N, (gammaChainCoeff c N lam : ℂ) * cexp (-(I * lam * t)) := by
  rw [chainZ_eq_spinSum]
  simp_rw [prod_gammaSiteField_eq]
  rw [← sum_fiberwise_of_maps_to (g := gammaSpinFrequency) (t := gammaChainFrequencies N)
    (fun S hS => mem_image_of_mem _ hS)]
  refine sum_congr rfl fun lam _ => ?_
  rw [gammaChainCoeff, Complex.ofReal_sum, sum_mul]
  refine sum_congr rfl fun S hS => ?_
  rw [(mem_filter.mp hS).2]

/-! ### Uniqueness of exponential-sum coefficients -/

/-- The character `t ↦ e^{-iλt}` of the additive group of reals. -/
def realExpCharacter (lam : ℝ) : Multiplicative ℝ →* ℂ where
  toFun t := cexp (-(I * lam * (Multiplicative.toAdd t : ℝ)))
  map_one' := by simp
  map_mul' s t := by
    rw [← Complex.exp_add]
    congr 1
    simp only [toAdd_mul, Complex.ofReal_add]
    ring

theorem realExpCharacter_injective : Function.Injective realExpCharacter := by
  intro lam mu h
  by_contra hne
  have hd : lam - mu ≠ 0 := sub_ne_zero.mpr hne
  have he := congrArg (fun χ : Multiplicative ℝ →* ℂ => χ (Multiplicative.ofAdd (π / (lam - mu)))) h
  simp only [realExpCharacter, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at he
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have him := congrArg Complex.im hn
  simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat] at him
  have hkey : (lam - mu) * (π / (lam - mu)) = π := mul_div_cancel₀ π hd
  have hpi : (π : ℝ) * (2 * (n : ℝ) + 1) = 0 := by nlinarith [hkey]
  have h2n : (2 * (n : ℝ) + 1) = 0 := (mul_eq_zero.mp hpi).resolve_left Real.pi_ne_zero
  have : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast h2n
  omega

/-- Exponentials with distinct real frequencies are linearly independent. -/
theorem expSum_coeff_eq_zero (Λ : Finset ℝ) (a : ℝ → ℂ)
    (h : ∀ t : ℝ, ∑ lam ∈ Λ, a lam * cexp (-(I * lam * t)) = 0) : ∀ lam ∈ Λ, a lam = 0 := by
  have hli := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp realExpCharacter
    realExpCharacter_injective
  intro lam hlam
  refine linearIndependent_iff'.mp hli Λ a ?_ lam hlam
  funext t
  simpa [Finset.sum_apply, realExpCharacter] using h (Multiplicative.toAdd t)

/-- Every finite exponential-sum representation of the Γ-site chain has the spin fiber sums as
coefficients: zero off the spin-word frequencies, and `C_λ` on them. -/
theorem gammaChain_expSum_coeff_eq (c : ℕ → ℝ) (N : ℕ) (Λ : Finset ℝ) (a : ℝ → ℂ)
    (hrep : ∀ t : ℝ, chainZ c (chainExpField gammaFreq (t : ℂ)) N =
      ∑ lam ∈ Λ, a lam * cexp (-(I * lam * t))) (lam : ℝ) (hlam : lam ∈ Λ) :
    a lam = if lam ∈ gammaChainFrequencies N then (gammaChainCoeff c N lam : ℂ) else 0 := by
  classical
  let F := gammaChainFrequencies N
  let d : ℝ → ℂ := fun x =>
    (if x ∈ Λ then a x else 0) - (if x ∈ F then (gammaChainCoeff c N x : ℂ) else 0)
  have hzero : ∀ t : ℝ, ∑ x ∈ Λ ∪ F, d x * cexp (-(I * x * t)) = 0 := by
    intro t
    have hΛ : ∑ x ∈ Λ ∪ F, (if x ∈ Λ then a x else 0) * cexp (-(I * x * t)) =
        ∑ x ∈ Λ, a x * cexp (-(I * x * t)) := by
      simp_rw [ite_mul, zero_mul]
      rw [sum_ite_mem, union_inter_cancel_left]
    have hF : ∑ x ∈ Λ ∪ F, (if x ∈ F then (gammaChainCoeff c N x : ℂ) else 0) *
        cexp (-(I * x * t)) = ∑ x ∈ F, (gammaChainCoeff c N x : ℂ) * cexp (-(I * x * t)) := by
      simp_rw [ite_mul, zero_mul]
      rw [sum_ite_mem, union_inter_cancel_right]
    simp only [d, sub_mul, sum_sub_distrib, hΛ, hF, ← hrep t, ← gammaChainZ_eq_frequencySum]
    exact sub_self _
  have hd := expSum_coeff_eq_zero (Λ ∪ F) d hzero lam (mem_union_left _ hlam)
  simp only [d, if_pos hlam] at hd
  exact sub_eq_zero.mp hd

theorem gammaSpinWeight_nonneg {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (N : ℕ) (S : Finset ℕ) :
    0 ≤ gammaSpinWeight c N S :=
  prod_nonneg fun k _ => hc k

/-- The fugacity-positive walls. -/
def gammaActiveWalls (c : ℕ → ℝ) (N : ℕ) : Finset ℕ := (range N).filter (fun k => 0 < c k)

theorem gammaSpinWeight_ne_zero_iff {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (N : ℕ) (S : Finset ℕ) :
    gammaSpinWeight c N S ≠ 0 ↔ ∀ i < N, GammaSpinWallAt S i → i ∈ gammaActiveWalls c N := by
  unfold gammaSpinWeight
  rw [prod_ne_zero_iff]
  constructor
  · intro h i hi hw
    exact mem_filter.mpr ⟨mem_range.mpr hi,
      lt_of_le_of_ne (hc i) (Ne.symm (h i (mem_gammaSpinWalls.mpr ⟨hi, hw⟩)))⟩
  · intro h i hi
    obtain ⟨hiN, hw⟩ := mem_gammaSpinWalls.mp hi
    exact (mem_filter.mp (h i hiN hw)).2.ne'

/-- With nonnegative fugacities the coefficient at a spin-word frequency is positive exactly when
some word with that frequency has all its walls active; no cancellation occurs. -/
theorem gammaChainCoeff_ne_zero_iff {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (N : ℕ) (lam : ℝ) :
    gammaChainCoeff c N lam ≠ 0 ↔
      ∃ S, GammaSpinWordAllowed N (gammaActiveWalls c N) S ∧ gammaSpinFrequency S = lam := by
  unfold gammaChainCoeff
  rw [Ne, sum_eq_zero_iff_of_nonneg (fun S _ => gammaSpinWeight_nonneg hc N S)]
  push_neg
  constructor
  · rintro ⟨S, hS, hw⟩
    obtain ⟨hSp, hfreq⟩ := mem_filter.mp hS
    exact ⟨S, ⟨mem_powerset.mp hSp, (gammaSpinWeight_ne_zero_iff hc N S).mp hw⟩, hfreq⟩
  · rintro ⟨S, ⟨hSsub, hwalls⟩, hfreq⟩
    exact ⟨S, mem_filter.mpr ⟨mem_powerset.mpr hSsub, hfreq⟩,
      (gammaSpinWeight_ne_zero_iff hc N S).mpr hwalls⟩

/-- **Exact Fourier spectrum.**  In every finite exponential-sum representation of the Γ-site
chain with nonnegative fugacities, the frequencies with nonzero coefficient are exactly the
frequencies `log q(S)` of the spin words whose walls are all active. -/
theorem gammaChain_spectrum_iff {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (N : ℕ) (Λ : Finset ℝ)
    (a : ℝ → ℂ)
    (hrep : ∀ t : ℝ, chainZ c (chainExpField gammaFreq (t : ℂ)) N =
      ∑ lam ∈ Λ, a lam * cexp (-(I * lam * t))) (lam : ℝ) (hlam : lam ∈ Λ) :
    a lam ≠ 0 ↔
      ∃ S, GammaSpinWordAllowed N (gammaActiveWalls c N) S ∧ gammaSpinFrequency S = lam := by
  rw [gammaChain_expSum_coeff_eq c N Λ a hrep lam hlam, ← gammaChainCoeff_ne_zero_iff hc N lam]
  split_ifs with hF
  · exact_mod_cast Iff.rfl
  · simp only [ne_eq, not_true_eq_false, false_iff]
    intro hne
    obtain ⟨S, ⟨hS, _⟩, hfreq⟩ := (gammaChainCoeff_ne_zero_iff hc N lam).mp hne
    exact hF (hfreq ▸ mem_image_of_mem _ (mem_powerset.mpr hS))

/-! ### Integrality of block products: the converse direction -/

theorem prod_range_gammaSiteRatio (k : ℕ) :
    ∏ i ∈ range (k + 1), gammaSiteRatio i = ((k + 2 : ℕ) : ℚ) := by
  induction k with
  | zero => norm_num [gammaSiteRatio]
  | succ k ih =>
    rw [prod_range_succ, ih]
    unfold gammaSiteRatio
    push_cast
    field_simp
    ring

/-- A finite spin word whose walls are pairwise in ordered divisibility has integral frequency
base: each maximal minus block `(a, b]` contributes `(b+2)/(a+2) ∈ ℕ`, an initial block `[0, b]`
contributes `b + 2`. -/
theorem gammaSpinWordRatio_eq_nat_of_wall_dvd :
    ∀ S : Finset ℕ, (∀ j k, j < k → GammaSpinWallAt S j → GammaSpinWallAt S k → j + 2 ∣ k + 2) →
      ∃ n : ℕ, 0 < n ∧ gammaSpinWordRatio S = n := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp [gammaSpinWordRatio]⟩
  set b := S.max' hne with hbdef
  have hbS : b ∈ S := S.max'_mem hne
  have hbmax : ∀ x ∈ S, x ≤ b := fun x hx => S.le_max' x hx
  by_cases hgap : ∃ a, a < b ∧ a ∉ S
  · let T := (range b).filter (fun x => x ∉ S)
    have hTne : T.Nonempty := by
      obtain ⟨a, hab, haS⟩ := hgap
      exact ⟨a, mem_filter.mpr ⟨mem_range.mpr hab, haS⟩⟩
    set a := T.max' hTne with hadef
    have haT := mem_filter.mp (T.max'_mem hTne)
    have hab : a < b := mem_range.mp haT.1
    have haS : a ∉ S := haT.2
    have hblock : ∀ x, a < x → x ≤ b → x ∈ S := by
      intro x hax hxb
      by_contra hxS
      rcases eq_or_lt_of_le hxb with hxe | hxb'
      · exact hxS (hxe ▸ hbS)
      · have hxT : x ∈ T := mem_filter.mpr ⟨mem_range.mpr hxb', hxS⟩
        have := T.le_max' x hxT
        omega
    let S' := S.filter (· < a)
    have hdisj : Disjoint S' (Ico (a + 1) (b + 1)) := by
      rw [disjoint_left]
      intro x hx hx'
      have := (mem_filter.mp hx).2
      have := (mem_Ico.mp hx').1
      omega
    have hsplit : S = S' ∪ Ico (a + 1) (b + 1) := by
      ext x
      simp only [mem_union, mem_filter, mem_Ico, S']
      constructor
      · intro hx
        have hxb := hbmax x hx
        rcases lt_trichotomy x a with hxa | hxa | hxa
        · exact Or.inl ⟨hx, hxa⟩
        · exact absurd (hxa ▸ hx) haS
        · exact Or.inr ⟨hxa, by omega⟩
      · rintro (⟨hx, _⟩ | ⟨h1, h2⟩)
        · exact hx
        · exact hblock x (by omega) (by omega)
    have hratio : gammaSpinWordRatio S =
        gammaSpinWordRatio S' * (((b + 2 : ℕ) : ℚ) / (a + 2)) := by
      unfold gammaSpinWordRatio
      conv_lhs => rw [hsplit]
      rw [prod_union hdisj, prod_gammaSiteRatio_Ico a b hab.le]
    have hssub : S' ⊂ S := by
      refine ⟨filter_subset _ _, fun h => ?_⟩
      have := (mem_filter.mp (h hbS)).2
      omega
    have hwalls' : ∀ i, GammaSpinWallAt S' i → GammaSpinWallAt S i := by
      intro i hi
      unfold GammaSpinWallAt at hi ⊢
      simp only [S', mem_filter, not_and, not_lt] at hi
      rcases hi with ⟨⟨hiS, hia⟩, hi1⟩ | ⟨hi, ⟨hi1S, hi1a⟩⟩
      · left
        refine ⟨hiS, fun h => ?_⟩
        have := hi1 h
        have : i + 1 = a := by omega
        exact haS (this ▸ h)
      · right
        exact ⟨fun h => by have := hi h; omega, hi1S⟩
    obtain ⟨n, hn, hq⟩ := ih S' hssub
      (fun j k hjk hj hk => hS j k hjk (hwalls' j hj) (hwalls' k hk))
    have hwa : GammaSpinWallAt S a := Or.inr ⟨haS, hblock (a + 1) (by omega) (by omega)⟩
    have hwb : GammaSpinWallAt S b := Or.inl ⟨hbS, fun h => by have := hbmax _ h; omega⟩
    obtain ⟨m, hm⟩ := hS a b hab hwa hwb
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm
        omega
      · exact h0
    refine ⟨n * m, Nat.mul_pos hn hm0, ?_⟩
    rw [hratio, hq, hm]
    push_cast
    field_simp
  · push_neg at hgap
    have hS' : S = range (b + 1) := by
      ext x
      simp only [mem_range]
      constructor
      · intro hx
        exact Nat.lt_succ_of_le (hbmax x hx)
      · intro hx
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hxb | hxb
        · exact hgap x hxb
        · exact hxb ▸ hbS
    refine ⟨b + 2, by omega, ?_⟩
    rw [gammaSpinWordRatio, hS', prod_range_gammaSiteRatio]

/-- Complementing inside the sites `0..N` keeps every wall below `N`. -/
theorem gammaSpinWallAt_sdiff_iff {N : ℕ} {S : Finset ℕ} {i : ℕ} (hi : i < N) :
    GammaSpinWallAt (range (N + 1) \ S) i ↔ GammaSpinWallAt S i := by
  unfold GammaSpinWallAt
  simp only [mem_sdiff, mem_range]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega

/-- **Converse.**  If the allowed walls form an ordered divisibility chain, every allowed spin word
has frequency base in the dual alphabet `ℕ ∪ M/ℕ`, `M = N + 2`. -/
theorem gammaSpinWord_mem_dualAlphabet_of_divisibility_chain (N : ℕ) (W : Finset ℕ)
    (hchain : ∀ j ∈ W, ∀ k ∈ W, j < k → j + 2 ∣ k + 2) (S : Finset ℕ)
    (hS : GammaSpinWordAllowed N W S) :
    InPrimePivotDualAlphabet (N + 2) (gammaSpinWordRatio S) := by
  obtain ⟨hSsub, hSW⟩ := hS
  have hhigh (T : Finset ℕ) (hT : T ⊆ range (N + 1)) (hNT : N ∉ T) (i : ℕ)
      (hw : GammaSpinWallAt T i) : i < N := by
    by_contra hiN
    push_neg at hiN
    unfold GammaSpinWallAt at hw
    rcases hw with ⟨hiT, _⟩ | ⟨_, hiT⟩
    · have := mem_range.mp (hT hiT)
      exact hNT (show i = N by omega ▸ hiT)
    · have := mem_range.mp (hT hiT)
      omega
  by_cases hN : N ∈ S
  · let Sc := range (N + 1) \ S
    have hScsub : Sc ⊆ range (N + 1) := sdiff_subset
    have hNSc : N ∉ Sc := fun h => (mem_sdiff.mp h).2 hN
    obtain ⟨n, hn, hq⟩ := gammaSpinWordRatio_eq_nat_of_wall_dvd Sc (by
      intro j k hjk hj hk
      have hjN := hhigh Sc hScsub hNSc j hj
      have hkN := hhigh Sc hScsub hNSc k hk
      exact hchain j (hSW j hjN ((gammaSpinWallAt_sdiff_iff hjN).mp hj))
        k (hSW k hkN ((gammaSpinWallAt_sdiff_iff hkN).mp hk)) hjk)
    have hprod : gammaSpinWordRatio Sc * gammaSpinWordRatio S = ((N + 2 : ℕ) : ℚ) := by
      unfold gammaSpinWordRatio
      rw [prod_sdiff hSsub, prod_range_gammaSiteRatio]
    right
    refine ⟨n, hn, ?_⟩
    rw [hq] at hprod
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [eq_div_iff hn', mul_comm]
    exact_mod_cast hprod
  · obtain ⟨n, hn, hq⟩ := gammaSpinWordRatio_eq_nat_of_wall_dvd S (by
      intro j k hjk hj hk
      have hjN := hhigh S hSsub hN j hj
      have hkN := hhigh S hSsub hN k hk
      exact hchain j (hSW j hjN hj) k (hSW k hkN hk) hjk)
    exact Or.inl ⟨n, hn, hq⟩

/-- **Prime-pivot classification.**  At a prime pivot `M = N + 2`, every spin word with allowed
walls has frequency base in the dual alphabet `ℕ ∪ M/ℕ` iff the allowed wall labels `k + 2`
form an ordered divisibility chain. -/
theorem primePivot_spinSpectrum_dual_iff_divisibility_chain (N : ℕ) (hM : (N + 2).Prime)
    (W : Finset ℕ) (hW : W ⊆ range N) :
    (∀ S, GammaSpinWordAllowed N W S → InPrimePivotDualAlphabet (N + 2) (gammaSpinWordRatio S)) ↔
      ∀ j ∈ W, ∀ k ∈ W, j < k → j + 2 ∣ k + 2 :=
  ⟨primePivot_spinSpectrum_forces_divisibility_chain N hM W hW,
    fun hchain S hS => gammaSpinWord_mem_dualAlphabet_of_divisibility_chain N W hchain S hS⟩

theorem gammaSpinFrequency_eq_log_iff (S : Finset ℕ) {q : ℚ} (hq : 0 < q) :
    gammaSpinFrequency S = Real.log (q : ℝ) ↔ gammaSpinWordRatio S = q := by
  unfold gammaSpinFrequency
  constructor
  · intro h
    have hpos : (0 : ℝ) < (gammaSpinWordRatio S : ℝ) := by exact_mod_cast gammaSpinWordRatio_pos S
    have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact_mod_cast Real.log_injOn_pos hpos hq' h
  · intro h
    rw [h]

theorem inPrimePivotDualAlphabet_pos {M : ℕ} (hM : 0 < M) {q : ℚ}
    (hq : InPrimePivotDualAlphabet M q) : 0 < q := by
  rcases hq with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · exact_mod_cast hn
  · have : (0 : ℚ) < M := by exact_mod_cast hM
    have : (0 : ℚ) < n := by exact_mod_cast hn
    positivity

/-- **The Γ-site spectrum at a prime pivot.**  For nonnegative fugacities and any finite
exponential-sum representation of the chain, every frequency with nonzero coefficient lies in the
logarithmic dual alphabet `log ℕ ∪ log (M/ℕ)` iff the active walls form an ordered divisibility
chain. -/
theorem gammaChain_primePivot_dualSpectrum_iff {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (N : ℕ)
    (hM : (N + 2).Prime) (Λ : Finset ℝ) (a : ℝ → ℂ)
    (hrep : ∀ t : ℝ, chainZ c (chainExpField gammaFreq (t : ℂ)) N =
      ∑ lam ∈ Λ, a lam * cexp (-(I * lam * t))) :
    (∀ lam ∈ Λ, a lam ≠ 0 →
        ∃ q, InPrimePivotDualAlphabet (N + 2) q ∧ lam = Real.log (q : ℝ)) ↔
      ∀ j ∈ gammaActiveWalls c N, ∀ k ∈ gammaActiveWalls c N, j < k → j + 2 ∣ k + 2 := by
  have hWsub : gammaActiveWalls c N ⊆ range N := filter_subset _ _
  rw [← primePivot_spinSpectrum_dual_iff_divisibility_chain N hM _ hWsub]
  constructor
  · intro h S hS
    have hlam : gammaSpinFrequency S ∈ Λ := by
      by_contra hnot
      have hrep' : ∀ t : ℝ, chainZ c (chainExpField gammaFreq (t : ℂ)) N =
          ∑ lam ∈ insert (gammaSpinFrequency S) Λ,
            (if lam ∈ Λ then a lam else 0) * cexp (-(I * lam * t)) := by
        intro t
        rw [sum_insert hnot, if_neg hnot, zero_mul, zero_add, hrep t]
        refine sum_congr rfl fun lam hl => ?_
        rw [if_pos hl]
      have hne := (gammaChain_spectrum_iff hc N _ _ hrep' (gammaSpinFrequency S)
        (mem_insert_self _ _)).mpr ⟨S, hS, rfl⟩
      exact hne (if_neg hnot)
    have hne := (gammaChain_spectrum_iff hc N Λ a hrep _ hlam).mpr ⟨S, hS, rfl⟩
    obtain ⟨q, hq, hfreq⟩ := h _ hlam hne
    have hqpos := inPrimePivotDualAlphabet_pos (by omega) hq
    rwa [(gammaSpinFrequency_eq_log_iff S hqpos).mp hfreq]
  · intro h lam hlam hne
    obtain ⟨S, hS, hfreq⟩ := (gammaChain_spectrum_iff hc N Λ a hrep lam hlam).mp hne
    exact ⟨gammaSpinWordRatio S, h S hS, hfreq ▸ rfl⟩

/-! ### The wall budget -/

/-- An ordered divisibility chain of wall labels `k + 2 ≥ 2` with `r` elements has an element of
size at least `2 ^ r`: each strict divisibility step at least doubles. -/
theorem exists_two_pow_card_le_of_divisibility_chain (W : Finset ℕ)
    (hchain : ∀ j ∈ W, ∀ k ∈ W, j < k → j + 2 ∣ k + 2) (hne : W.Nonempty) :
    ∃ k ∈ W, 2 ^ W.card ≤ k + 2 := by
  induction W using Finset.induction_on_max with
  | empty => exact absurd hne not_nonempty_empty
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has]
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · exact ⟨a, mem_insert_self _ _, by simp⟩
    · obtain ⟨k, hks, hk⟩ := ih (fun j hj k hk => hchain j (mem_insert_of_mem hj) k
        (mem_insert_of_mem hk)) hsne
      refine ⟨a, mem_insert_self _ _, ?_⟩
      obtain ⟨m, hm⟩ := hchain k (mem_insert_of_mem hks) a (mem_insert_self _ _) (hlt k hks)
      have hka := hlt k hks
      have hm2 : 2 ≤ m := by
        by_contra h
        interval_cases m <;> omega
      rw [pow_succ, hm]
      nlinarith

/-- **Wall budget.**  An ordered divisibility chain of walls below `N` has `2 ^ r ≤ N + 1`, so
`2 ^ r < M = N + 2` and `r ≤ ⌊log₂ (N + 1)⌋`. -/
theorem two_pow_card_le_of_divisibility_chain (N : ℕ) (W : Finset ℕ) (hW : W ⊆ range N)
    (hchain : ∀ j ∈ W, ∀ k ∈ W, j < k → j + 2 ∣ k + 2) :
    2 ^ W.card ≤ N + 1 ∧ W.card ≤ Nat.log 2 (N + 1) := by
  have hpow : 2 ^ W.card ≤ N + 1 := by
    rcases W.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨k, hk, hle⟩ := exists_two_pow_card_le_of_divisibility_chain W hchain hne
      have := mem_range.mp (hW hk)
      omega
  exact ⟨hpow, Nat.le_log_of_pow_le one_lt_two hpow⟩

/-- At a prime pivot `M = N + 2`, the active walls of a ferromagnetic Γ-site chain whose complete
spectrum lies in the dual alphabet number at most `⌊log₂ (M - 1)⌋`, and `2 ^ r < M`. -/
theorem gammaChain_primePivot_dualSpectrum_wall_budget {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (N : ℕ)
    (hM : (N + 2).Prime) (Λ : Finset ℝ) (a : ℝ → ℂ)
    (hrep : ∀ t : ℝ, chainZ c (chainExpField gammaFreq (t : ℂ)) N =
      ∑ lam ∈ Λ, a lam * cexp (-(I * lam * t)))
    (hdual : ∀ lam ∈ Λ, a lam ≠ 0 →
      ∃ q, InPrimePivotDualAlphabet (N + 2) q ∧ lam = Real.log (q : ℝ)) :
    2 ^ (gammaActiveWalls c N).card < N + 2 ∧
      (gammaActiveWalls c N).card ≤ Nat.log 2 (N + 1) := by
  have hchain := (gammaChain_primePivot_dualSpectrum_iff hc N hM Λ a hrep).mp hdual
  obtain ⟨h1, h2⟩ := two_pow_card_le_of_divisibility_chain N _ (filter_subset _ _) hchain
  exact ⟨by omega, h2⟩

/-- **Sharpness.**  The walls `k = 2^(j+1) - 2`, `j < ⌊log₂ (N + 1)⌋`, form an ordered
divisibility chain below `N` of exactly that size. -/
theorem exists_divisibility_chain_card_eq_log (N : ℕ) :
    ∃ W : Finset ℕ, W ⊆ range N ∧ (∀ j ∈ W, ∀ k ∈ W, j < k → j + 2 ∣ k + 2) ∧
      W.card = Nat.log 2 (N + 1) := by
  let f : ℕ → ℕ := fun j => 2 ^ (j + 1) - 2
  have hf2 (j : ℕ) : f j + 2 = 2 ^ (j + 1) := by
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [f]
    omega
  have hfmono : StrictMono f := by
    intro i j hij
    have := hf2 i
    have := hf2 j
    have : 2 ^ (i + 1) < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨(range (Nat.log 2 (N + 1))).image f, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
    have hjl := mem_range.mp hj
    have hpow : 2 ^ (j + 1) ≤ N + 1 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hjl) (Nat.pow_log_le_self 2 (by omega))
    have := hf2 j
    exact mem_range.mpr (by omega)
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    rw [hf2, hf2]
    exact Nat.pow_dvd_pow 2 (by have := hfmono.lt_iff_lt.mp hxy; omega)
  · rw [card_image_of_injective _ hfmono.injective, card_range]

/-! ### Signed fugacities: the two-wall coefficient polynomial -/

/-- The coefficient of the frequency base `q`, as a polynomial in independent fugacity variables
`X_k`. -/
def gammaChainCoeffPoly (N : ℕ) (q : ℚ) : MvPolynomial ℕ ℤ :=
  ∑ S ∈ (range (N + 1)).powerset.filter (fun S => gammaSpinWordRatio S = q),
    ∏ k ∈ gammaSpinWalls N S, MvPolynomial.X k

/-- Evaluating the coefficient polynomial at real fugacities gives the Fourier coefficient of the
chain at `log q`. -/
theorem eval_gammaChainCoeffPoly (c : ℕ → ℝ) (N : ℕ) {q : ℚ} (hq : 0 < q) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) c (gammaChainCoeffPoly N q) =
      gammaChainCoeff c N (Real.log (q : ℝ)) := by
  unfold gammaChainCoeffPoly gammaChainCoeff gammaSpinWeight
  rw [MvPolynomial.eval₂_sum]
  have hfilter : (range (N + 1)).powerset.filter (fun S => gammaSpinWordRatio S = q) =
      (range (N + 1)).powerset.filter (fun S => gammaSpinFrequency S = Real.log (q : ℝ)) := by
    ext S
    simp only [mem_filter, gammaSpinFrequency_eq_log_iff S hq]
  rw [hfilter]
  refine sum_congr rfl fun S _ => ?_
  rw [MvPolynomial.eval₂_prod]
  simp

/-- A spin word on sites `0..N` is determined by its walls and its first spin. -/
theorem eq_of_gammaSpinWalls_eq {N : ℕ} {S T : Finset ℕ} (hS : S ⊆ range (N + 1))
    (hT : T ⊆ range (N + 1)) (hw : gammaSpinWalls N S = gammaSpinWalls N T)
    (h0 : 0 ∈ S ↔ 0 ∈ T) : S = T := by
  have hstep : ∀ x, x ≤ N → (x ∈ S ↔ x ∈ T) := by
    intro x
    induction x with
    | zero => exact fun _ => h0
    | succ x ih =>
      intro hx
      have hxS := ih (by omega)
      have hwx : GammaSpinWallAt S x ↔ GammaSpinWallAt T x := by
        have := congrArg (fun F => x ∈ F) hw
        simp only [mem_gammaSpinWalls, eq_iff_iff] at this
        constructor
        · intro h
          exact (this.mp ⟨by omega, h⟩).2
        · intro h
          exact (this.mpr ⟨by omega, h⟩).2
      unfold GammaSpinWallAt at hwx
      tauto
  ext x
  by_cases hx : x ≤ N
  · exact hstep x hx
  · constructor
    · intro h
      have := mem_range.mp (hS h)
      omega
    · intro h
      have := mem_range.mp (hT h)
      omega

theorem gammaSpinWalls_sdiff (N : ℕ) (S : Finset ℕ) :
    gammaSpinWalls N (range (N + 1) \ S) = gammaSpinWalls N S := by
  ext i
  simp only [mem_gammaSpinWalls]
  constructor
  · rintro ⟨hi, hw⟩
    exact ⟨hi, (gammaSpinWallAt_sdiff_iff hi).mp hw⟩
  · rintro ⟨hi, hw⟩
    exact ⟨hi, (gammaSpinWallAt_sdiff_iff hi).mpr hw⟩

theorem gammaSpinWalls_interval (N j k : ℕ) (hjk : j < k) (hkN : k < N) :
    gammaSpinWalls N (Ico (j + 1) (k + 1)) = {j, k} := by
  ext i
  rw [mem_gammaSpinWalls, gammaSpinWallAt_interval_iff j k i hjk, mem_insert, mem_singleton]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by omega, h⟩

theorem sum_single_one_eq_pair_iff {T : Finset ℕ} {j k : ℕ} (hjk : j ≠ k) :
    (∑ w ∈ T, Finsupp.single w 1) = Finsupp.single j 1 + Finsupp.single k 1 ↔ T = {j, k} := by
  constructor
  · intro h
    ext x
    have hx := congrArg (fun f : ℕ →₀ ℕ => f x) h
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
      Finsupp.coe_add, Pi.add_apply] at hx
    rw [sum_ite_eq'] at hx
    rw [mem_insert, mem_singleton]
    by_cases hxT : x ∈ T
    · simp only [hxT, if_true] at hx
      by_contra hne
      push_neg at hne
      rw [if_neg (Ne.symm hne.1), if_neg (Ne.symm hne.2)] at hx
      omega
    · simp only [hxT, if_false] at hx
      constructor
      · intro h
        exact absurd h hxT
      · rintro (rfl | rfl)
        · rw [if_pos rfl] at hx
          omega
        · rw [if_pos rfl] at hx
          omega
  · rintro rfl
    rw [sum_pair hjk]

/-- **Nonzero signed coefficient.**  At a prime pivot `M = N + 2`, for walls `j < k < N`, the
coefficient polynomial of the two-wall frequency base `(k+2)/(j+2)` has coefficient one at the
monomial `X_j X_k`: only the minus interval `(j, k]` contributes, because its complement has
frequency base `M (j+2)/(k+2) ≠ (k+2)/(j+2)`. -/
theorem gammaChainCoeffPoly_coeff_twoWall (N j k : ℕ) (hM : (N + 2).Prime) (hjk : j < k)
    (hkN : k < N) :
    MvPolynomial.coeff (Finsupp.single j 1 + Finsupp.single k 1)
      (gammaChainCoeffPoly N (((k + 2 : ℕ) : ℚ) / (j + 2))) = 1 := by
  classical
  let I₀ : Finset ℕ := Ico (j + 1) (k + 1)
  have hI₀sub : I₀ ⊆ range (N + 1) := by
    intro x hx
    have := mem_Ico.mp hx
    exact mem_range.mpr (by omega)
  have hmono (T : Finset ℕ) : (∏ w ∈ T, MvPolynomial.X w : MvPolynomial ℕ ℤ) =
      MvPolynomial.monomial (∑ w ∈ T, Finsupp.single w 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    rfl
  unfold gammaChainCoeffPoly
  rw [MvPolynomial.coeff_sum]
  simp_rw [hmono, MvPolynomial.coeff_monomial]
  have hjk' : j ≠ k := hjk.ne
  simp_rw [sum_single_one_eq_pair_iff hjk']
  rw [sum_boole]
  have hset : ((range (N + 1)).powerset.filter
      (fun S => gammaSpinWordRatio S = ((k + 2 : ℕ) : ℚ) / (j + 2))).filter
        (fun S => {j, k} = gammaSpinWalls N S) = {I₀} := by
    ext S
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨⟨hS, hq⟩, hw⟩
      have hwI : gammaSpinWalls N S = gammaSpinWalls N I₀ := by
        rw [← hw, gammaSpinWalls_interval N j k hjk hkN]
      have h0I : 0 ∉ I₀ := by simp [I₀]
      by_cases h0 : 0 ∈ S
      · exfalso
        have hSc : range (N + 1) \ S = I₀ := by
          apply eq_of_gammaSpinWalls_eq sdiff_subset hI₀sub
          · rw [gammaSpinWalls_sdiff, hwI]
          · simp [h0, h0I]
        have hprod : gammaSpinWordRatio (range (N + 1) \ S) * gammaSpinWordRatio S =
            ((N + 2 : ℕ) : ℚ) := by
          unfold gammaSpinWordRatio
          rw [prod_sdiff hS, prod_range_gammaSiteRatio]
        rw [hSc, hq] at hprod
        have hI₀q : gammaSpinWordRatio I₀ = ((k + 2 : ℕ) : ℚ) / (j + 2) :=
          gammaSpinWordRatio_interval j k hjk.le
        rw [hI₀q] at hprod
        have hj2 : ((j : ℚ) + 2) ≠ 0 := by positivity
        have hnat : (k + 2) * (k + 2) = (N + 2) * ((j + 2) * (j + 2)) := by
          have h' : (((k + 2 : ℕ) : ℚ)) * ((k + 2 : ℕ) : ℚ) =
              ((N + 2 : ℕ) : ℚ) * (((j : ℚ) + 2) * ((j : ℚ) + 2)) := by
            field_simp at hprod
            linear_combination hprod
          exact_mod_cast h'
        have hdvd : N + 2 ∣ (k + 2) * (k + 2) := ⟨_, hnat⟩
        rcases (Nat.Prime.dvd_mul hM).mp hdvd with h | h <;>
          · have := Nat.le_of_dvd (by omega) h
            omega
      · exact eq_of_gammaSpinWalls_eq hS hI₀sub hwI (by simp [h0, h0I])
    · rintro rfl
      exact ⟨⟨hI₀sub, gammaSpinWordRatio_interval j k hjk.le⟩,
        (gammaSpinWalls_interval N j k hjk hkN).symm⟩
  rw [hset, card_singleton, Nat.cast_one]

/-- The two-wall coefficient polynomial is nonzero; for a nondividing pair its frequency is not
dual, so signed fugacities that cancel it lie on the zero set of a nonzero polynomial. -/
theorem gammaChainCoeffPoly_twoWall_ne_zero (N j k : ℕ) (hM : (N + 2).Prime) (hjk : j < k)
    (hkN : k < N) :
    gammaChainCoeffPoly N (((k + 2 : ℕ) : ℚ) / (j + 2)) ≠ 0 ∧
      (¬ j + 2 ∣ k + 2 →
        ¬ InPrimePivotDualAlphabet (N + 2) (((k + 2 : ℕ) : ℚ) / (j + 2))) := by
  refine ⟨fun h0 => ?_, fun hnd hdual => hnd ?_⟩
  · have := gammaChainCoeffPoly_coeff_twoWall N j k hM hjk hkN
    rw [h0, MvPolynomial.coeff_zero] at this
    exact zero_ne_one this
  · have h := (primePivot_twoWall_ratio_mem_iff_dvd (N + 2) (j + 2) (k + 2) hM (by omega)
      (by omega) (by omega)).mp
    exact h (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hdual)

end

end RHTower.LeeYangChain
