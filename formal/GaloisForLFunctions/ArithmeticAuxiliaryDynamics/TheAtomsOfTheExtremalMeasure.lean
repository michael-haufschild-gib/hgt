import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheExtremalFakePrimeMeasure
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The atoms of the extremal measure

The program of the best slope for a target `S` has an optimal real sawtooth, and every extremal fake prime measure lives where it is tight.

* **The sawteeth `r mod k`, `2 ≤ k ≤ K`, are linearly independent** on `[1, K]`. The difference of the sawtooth sum at `r` and `r − 1` is
  `Σ q_k − Σ_{k ∣ r} k q_k`, so vanishing on `[1, K]` forces `Σ q_k = 0` at `r = 1` and then `r q_r = 0` by induction on `r`.
* So the cost controls the weights: against the pronic measure the cost bounds the sawtooth sum at `r ≤ K` by `r (r + 1)` times the cost, and
  the weights are a bounded linear image of these values. **The minimum is attained.**
* **Complementary slackness.** For an optimal sawtooth `f` and any fake prime measure `u` of maximal mass, `Σ u(r) (f(r) − 1_S(r)) = 0`, and every
  term is nonnegative. So every atom sits at a residue where `f = 1` on `S` and `f = 0` off `S`.

So the extremal measure of level `K` is carried by the tight set of an optimal sawtooth: at most `K` of its residues, by Carathéodory.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The weights on the letters `2, …, K` given by a vector. -/
def weightsOf (K : ℕ) (v : Fin (K - 1) → ℝ) (k : ℕ) : ℝ :=
  if h : 2 ≤ k ∧ k - 2 < K - 1 then v ⟨k - 2, h.2⟩ else 0

private lemma mem_Icc_two_iff {K k : ℕ} (hK : 2 ≤ K) : k ∈ Icc 2 K ↔ 2 ≤ k ∧ k - 2 < K - 1 := by
  rw [mem_Icc]
  omega

/-- A sum over the letters `2, …, K` is a sum over the coordinates. -/
private lemma sum_Icc_two_eq_fin (g : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Icc 2 K, g k = ∑ i : Fin (K - 1), g ((i : ℕ) + 2) := by
  have hset : Icc 2 K = Ico 2 (K + 1) := by
    ext x
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hset, sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun i => g (i + 2)) (K - 1)]
  have hn : K + 1 - 2 = K - 1 := by omega
  rw [hn]
  exact sum_congr rfl fun i _ => by rw [add_comm]

private lemma weightsOf_fin {K : ℕ} (v : Fin (K - 1) → ℝ) (i : Fin (K - 1)) :
    weightsOf K v ((i : ℕ) + 2) = v i := by
  have h : 2 ≤ (i : ℕ) + 2 ∧ (i : ℕ) + 2 - 2 < K - 1 := ⟨by omega, by simp⟩
  rw [weightsOf, dif_pos h]
  congr 1

/-- The sawtooth sum of a vector, coordinatewise. -/
theorem saw_weightsOf (K : ℕ) (v : Fin (K - 1) → ℝ) (r : ℕ) :
    saw (weightsOf K v) K r = ∑ i : Fin (K - 1), v i * ((r % ((i : ℕ) + 2) : ℕ) : ℝ) := by
  rw [saw, sum_Icc_two_eq_fin]
  exact sum_congr rfl fun i _ => by rw [weightsOf_fin]

theorem objective_weightsOf (K : ℕ) (v : Fin (K - 1) → ℝ) :
    objective (weightsOf K v) K = ∑ i : Fin (K - 1), v i * Real.log (((i : ℕ) + 2 : ℕ) : ℝ) := by
  rw [objective, sum_Icc_two_eq_fin]
  exact sum_congr rfl fun i _ => by rw [weightsOf_fin]

/-- A real weight agrees with the weight of its coordinate vector on the letters. -/
private lemma saw_weightsOf_restrict {K : ℕ} (_hK : 2 ≤ K) (q : ℕ → ℝ) :
    (∀ r, saw (weightsOf K fun i => q ((i : ℕ) + 2)) K r = saw q K r) ∧
      objective (weightsOf K fun i => q ((i : ℕ) + 2)) K = objective q K := by
  constructor
  · intro r
    rw [saw_weightsOf, saw, sum_Icc_two_eq_fin]
  · rw [objective_weightsOf, objective, sum_Icc_two_eq_fin]

/-- The jump of a residue at `r = n + 1`. -/
private lemma mod_succ_sub {k n : ℕ} (hk : 2 ≤ k) :
    (((n + 1) % k : ℕ) : ℝ) - ((n % k : ℕ) : ℝ) = 1 - (if k ∣ n + 1 then (k : ℝ) else 0) := by
  have h1 : (n + 1) % k = (n % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < k)]
  have hlt : n % k < k := Nat.mod_lt n (by omega)
  by_cases hd : k ∣ n + 1
  · rw [if_pos hd]
    have h2 : (n + 1) % k = 0 := Nat.mod_eq_zero_of_dvd hd
    have h3 : n % k + 1 = k := by
      rw [h1] at h2
      have h4 : (n % k + 1) % k = 0 := h2
      rcases Nat.lt_or_ge (n % k + 1) k with h5 | h5
      · rw [Nat.mod_eq_of_lt h5] at h4
        omega
      · omega
    rw [h2]
    have : ((n % k : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : (n % k : ℕ) = k - 1 := by omega
      rw [this, Nat.cast_sub (by omega)]
      simp
    rw [this]
    push_cast
    ring
  · rw [if_neg hd, sub_zero]
    have h5 : n % k + 1 < k := by
      by_contra hge
      apply hd
      have h6 : n % k + 1 = k := by omega
      rw [Nat.dvd_iff_mod_eq_zero, h1, h6, Nat.mod_self]
    rw [h1, Nat.mod_eq_of_lt h5]
    push_cast
    ring

/-- **The sawteeth are linearly independent.** A sawtooth sum on the letters `2, …, K` that vanishes on `[1, K]` has zero weights. -/
theorem eq_zero_of_saw_eq_zero {K : ℕ} (hK : 2 ≤ K) {v : Fin (K - 1) → ℝ}
    (h : ∀ r, 1 ≤ r → r ≤ K → saw (weightsOf K v) K r = 0) : v = 0 := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, q = weightsOf K v := ⟨_, rfl⟩
  rw [← hq] at h
  -- The jumps of the sawtooth sum.
  have hjump : ∀ n, saw q K (n + 1) - saw q K n =
      ∑ k ∈ Icc 2 K, q k - ∑ k ∈ Icc 2 K, (if k ∣ n + 1 then (k : ℝ) * q k else 0) := by
    intro n
    rw [saw, saw, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [← mul_sub, mod_succ_sub (mem_Icc.mp hk).1]
    split_ifs <;> ring
  have hsaw0 : saw q K 0 = 0 := saw_zero q K
  have hQ : ∑ k ∈ Icc 2 K, q k = 0 := by
    have h1 := hjump 0
    rw [hsaw0, h 1 le_rfl (by omega), sub_zero] at h1
    have h2 : ∑ k ∈ Icc 2 K, (if k ∣ 0 + 1 then (k : ℝ) * q k else 0) = 0 :=
      sum_eq_zero fun k hk => by
        have := (mem_Icc.mp hk).1
        rw [if_neg (fun hd => by have := Nat.le_of_dvd one_pos hd; omega)]
    rw [h2, sub_zero] at h1
    linarith
  have hdiv : ∀ r, 1 ≤ r → r ≤ K → ∑ k ∈ Icc 2 K, (if k ∣ r then (k : ℝ) * q k else 0) = 0 := by
    intro r hr1 hrK
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    have h1 := hjump n
    rw [h (n + 1) hr1 hrK, hQ, zero_sub] at h1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hsaw0] at h1
      linarith
    · rw [h n hn (by omega)] at h1
      linarith
  -- Induction on `r`.
  have hzero : ∀ r, 2 ≤ r → r ≤ K → q r = 0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr2 hrK
      have h1 := hdiv r (by omega) hrK
      have hsplit : ∑ k ∈ Icc 2 K, (if k ∣ r then (k : ℝ) * q k else 0) = (r : ℝ) * q r := by
        rw [sum_eq_single_of_mem r (mem_Icc.mpr ⟨hr2, hrK⟩)]
        · rw [if_pos dvd_rfl]
        · intro k hk hne
          split_ifs with hkr
          · have hk2 := (mem_Icc.mp hk).1
            have hle := Nat.le_of_dvd (by omega) hkr
            rw [ih k (lt_of_le_of_ne hle hne) hk2 (hle.trans hrK), mul_zero]
          · rfl
      rw [hsplit] at h1
      have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hr0
      · exact h2
  funext i
  have := hzero ((i : ℕ) + 2) (by omega) (by have := i.2; omega)
  rw [hq, weightsOf_fin] at this
  exact this

/-- The sawtooth values on `[1, K]`, as a linear map. -/
def sawValues (K : ℕ) : (Fin (K - 1) → ℝ) →ₗ[ℝ] (Fin K → ℝ) where
  toFun v := fun r => saw (weightsOf K v) K ((r : ℕ) + 1)
  map_add' v w := by
    funext r
    simp only [saw_weightsOf, Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' a v := by
    funext r
    simp only [saw_weightsOf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

theorem sawValues_injective {K : ℕ} (hK : 2 ≤ K) : Function.Injective (sawValues K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  refine eq_zero_of_saw_eq_zero hK fun r hr1 hrK => ?_
  have h := congrFun hv ⟨r - 1, by omega⟩
  simp only [sawValues, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h
  rwa [show r - 1 + 1 = r by omega] at h

private lemma continuous_saw_weightsOf (K r : ℕ) :
    Continuous fun v : Fin (K - 1) → ℝ => saw (weightsOf K v) K r := by
  simp only [saw_weightsOf]
  fun_prop

private lemma continuous_objective_weightsOf (K : ℕ) :
    Continuous fun v : Fin (K - 1) → ℝ => objective (weightsOf K v) K := by
  simp only [objective_weightsOf]
  fun_prop

/-- **The program attains its value.** There is an optimal real sawtooth. -/
theorem exists_optimal_weights {K : ℕ} {S : Finset ℕ} (hK : 2 ≤ K) (hS : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K) :
    ∃ q : ℕ → ℝ, IsFeasible K S q ∧ objective q K = lpValue K S := by
  classical
  obtain ⟨C, hC, hanti⟩ := (LinearMap.injective_iff_antilipschitz (sawValues K)).mp (sawValues_injective hK)
  have hne : {x | ∃ q, IsFeasible K S q ∧ objective q K = x}.Nonempty := ⟨_, _, isFeasible_const hS, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = lpValue K S + 1 := ⟨_, rfl⟩
  -- The sublevel set of feasible vectors.
  obtain ⟨A, hA⟩ : ∃ A : Set (Fin (K - 1) → ℝ), A = {v | IsFeasible K S (weightsOf K v) ∧ objective (weightsOf K v) K ≤ M} :=
    ⟨_, rfl⟩
  have hAclosed : IsClosed A := by
    have hfeas : {v : Fin (K - 1) → ℝ | IsFeasible K S (weightsOf K v)} =
        (⋂ r ∈ (Ico 1 (lcmUpTo K) : Set ℕ), {v | 0 ≤ saw (weightsOf K v) K r}) ∩
          ⋂ r ∈ (S : Set ℕ), {v | 1 ≤ saw (weightsOf K v) K r} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, coe_Ico, Set.mem_Ico, mem_coe]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun r hr => h1 r hr.1 hr.2, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun r hr1 hr2 => h1 r ⟨hr1, hr2⟩, h2⟩
    have hsplit : A = {v : Fin (K - 1) → ℝ | IsFeasible K S (weightsOf K v)} ∩
        {v | objective (weightsOf K v) K ≤ M} := by
      rw [hA]
      rfl
    rw [hsplit, hfeas]
    refine ((isClosed_biInter fun r _ => ?_).inter (isClosed_biInter fun r _ => ?_)).inter ?_
    · exact isClosed_le continuous_const (continuous_saw_weightsOf K r)
    · exact isClosed_le continuous_const (continuous_saw_weightsOf K r)
    · exact isClosed_le (continuous_objective_weightsOf K) continuous_const
  -- Feasible vectors of bounded cost are bounded.
  have hAbdd : A ⊆ Metric.closedBall 0 (C * (M * (((K : ℝ) + 1) * ((K : ℝ) + 1)))) := by
    intro v hv
    rw [hA] at hv
    obtain ⟨hF, hobj⟩ := hv
    have hsum := (isFakePrimeMeasure_pronic K).hasSum_saw (weightsOf K v)
    have hterm : ∀ j : ℕ, 0 ≤ 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * saw (weightsOf K v) K (j + 1) := fun j =>
      mul_nonneg (by positivity) (hF.saw_nonneg _)
    have hobj0 : 0 ≤ objective (weightsOf K v) K := hsum.nonneg hterm
    have hM0 : 0 ≤ M := hobj0.trans hobj
    have hval : ‖sawValues K v‖ ≤ M * (((K : ℝ) + 1) * ((K : ℝ) + 1)) := by
      refine (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ M * (((K : ℝ) + 1) * ((K : ℝ) + 1)))).mpr fun r => ?_
      have hr := r.2
      have hpos := hF.saw_nonneg ((r : ℕ) + 1)
      have hle := le_hasSum hsum (r : ℕ) fun j _ => hterm j
      have hpron : (0 : ℝ) < (((r : ℕ) : ℝ) + 1) * (((r : ℕ) : ℝ) + 2) := by positivity
      have h1 : saw (weightsOf K v) K ((r : ℕ) + 1) ≤ M * ((((r : ℕ) : ℝ) + 1) * (((r : ℕ) : ℝ) + 2)) := by
        rw [one_div, inv_mul_le_iff₀ hpron] at hle
        nlinarith
      have h2 : (((r : ℕ) : ℝ) + 1) * (((r : ℕ) : ℝ) + 2) ≤ ((K : ℝ) + 1) * ((K : ℝ) + 1) := by
        have : ((r : ℕ) : ℝ) + 2 ≤ (K : ℝ) + 1 := by
          have : (r : ℕ) + 1 ≤ K := hr
          exact_mod_cast (by omega : (r : ℕ) + 2 ≤ K + 1)
        gcongr
      have h3 : M * ((((r : ℕ) : ℝ) + 1) * (((r : ℕ) : ℝ) + 2)) ≤ M * (((K : ℝ) + 1) * ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h2 hM0
      simp only [sawValues, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
      rw [abs_of_nonneg hpos]
      linarith
    have hnorm : ‖v‖ ≤ C * ‖sawValues K v‖ := by
      have h1 := hanti.le_mul_dist v 0
      simpa [dist_zero_right, map_zero] using h1
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖v‖ ≤ C * ‖sawValues K v‖ := hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hval (by positivity)
  have hAcompact : IsCompact A := (isCompact_closedBall _ _).of_isClosed_subset hAclosed hAbdd
  -- A feasible vector of cost below `M`.
  obtain ⟨x₀, ⟨q₀, hq₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (by linarith : lpValue K S < M)
  obtain ⟨hsaw₀, hobj₀⟩ := saw_weightsOf_restrict hK q₀
  have hmem₀ : (fun i : Fin (K - 1) => q₀ ((i : ℕ) + 2)) ∈ A := by
    rw [hA]
    refine ⟨⟨fun r h1 h2 => ?_, fun r hr => ?_⟩, ?_⟩
    · rw [hsaw₀]
      exact hq₀.nonneg r h1 h2
    · rw [hsaw₀]
      exact hq₀.target r hr
    · rw [hobj₀]
      exact hlt.le
  obtain ⟨v, hvA, hmin⟩ := hAcompact.exists_isMinOn ⟨_, hmem₀⟩ (continuous_objective_weightsOf K).continuousOn
  have hvA' := hvA
  rw [hA] at hvA'
  refine ⟨weightsOf K v, hvA'.1, le_antisymm ?_ (lpValue_le hvA'.1)⟩
  -- Every feasible cost below `M` is at least the minimum.
  by_contra hgt
  push Not at hgt
  obtain ⟨x, ⟨q, hq, rfl⟩, hlt2⟩ := exists_lt_of_csInf_lt hne
    (lt_min hgt (by linarith : lpValue K S < M))
  obtain ⟨hsaw, hobj⟩ := saw_weightsOf_restrict hK q
  have hmem : (fun i : Fin (K - 1) => q ((i : ℕ) + 2)) ∈ A := by
    rw [hA]
    refine ⟨⟨fun r h1 h2 => ?_, fun r hr => ?_⟩, ?_⟩
    · rw [hsaw]
      exact hq.nonneg r h1 h2
    · rw [hsaw]
      exact hq.target r hr
    · rw [hobj]
      exact (hlt2.trans_le (min_le_right _ _)).le
  have h1 := hmin hmem
  simp only [Set.mem_setOf_eq] at h1
  rw [hobj] at h1
  have h2 := hlt2.trans_le (min_le_left _ _)
  linarith

/-- The mass on a target as a sum over all residues. -/
private lemma hasSum_targetMass {S : Finset ℕ} (hS : ∀ r ∈ S, 1 ≤ r) (u : ℕ → ℝ) :
    HasSum (fun j => u j * (if j + 1 ∈ S then 1 else 0)) (targetMass u S) := by
  classical
  have hinj : Set.InjOn (fun r : ℕ => r - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hS a ha
    have h2 := hS b hb
    simp only at hab
    omega
  have hval : targetMass u S = ∑ j ∈ S.image (fun r => r - 1), u j * (if j + 1 ∈ S then 1 else 0) := by
    rw [targetMass, sum_image hinj]
    refine sum_congr rfl fun r hr => ?_
    have e : r - 1 + 1 = r := by have := hS r hr; omega
    simp [e, hr]
  rw [hval]
  refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
  have hj' : j + 1 ∉ S := fun h => hj (mem_image.mpr ⟨j + 1, h, by simp⟩)
  simp [hj']

/-- **The atoms sit where the optimal sawtooth is tight.** For an optimal real sawtooth `f` and a fake prime measure of maximal mass, every atom lies at a
residue where `f = 1` on the target and `f = 0` off it. -/
theorem saw_eq_of_atom {K : ℕ} {S : Finset ℕ} (hS : ∀ r ∈ S, 1 ≤ r) {q : ℕ → ℝ} (hq : IsFeasible K S q)
    (hopt : objective q K = lpValue K S) {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u)
    (hmax : targetMass u S = lpValue K S) {j : ℕ} (hj : 0 < u j) :
    saw q K (j + 1) = if j + 1 ∈ S then 1 else 0 := by
  have h1 := hu.hasSum_saw q
  have h2 := hasSum_targetMass hS u
  have h3 := h1.sub h2
  rw [hopt, hmax, sub_self] at h3
  have hnn : ∀ i, 0 ≤ u i * saw q K (i + 1) - u i * (if i + 1 ∈ S then 1 else 0) := by
    intro i
    rw [← mul_sub]
    refine mul_nonneg (hu.nonneg i) ?_
    split_ifs with h
    · linarith [hq.target (i + 1) h]
    · linarith [hq.saw_nonneg (i + 1)]
  have hle := le_hasSum h3 j fun i _ => hnn i
  have hz : u j * (saw q K (j + 1) - (if j + 1 ∈ S then 1 else 0)) = 0 := by
    rw [mul_sub]
    linarith [hnn j]
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h hj.ne'
  · linarith

/-- **The extremal measure lives on the tight set of an optimal sawtooth.** -/
theorem exists_extremal_on_tight_set {K : ℕ} {S : Finset ℕ} (hK : 2 ≤ K) (hS : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K) :
    ∃ (q : ℕ → ℝ) (u : ℕ → ℝ), IsFeasible K S q ∧ objective q K = lpValue K S ∧ IsFakePrimeMeasure K u ∧
      (∀ v : ℕ → ℝ, IsFakePrimeMeasure K v → targetMass v S ≤ targetMass u S) ∧
      ∀ j, 0 < u j → saw q K (j + 1) = if j + 1 ∈ S then 1 else 0 := by
  obtain ⟨q, hq, hopt⟩ := exists_optimal_weights hK hS
  obtain ⟨u, hu, -, hmax, -, hval⟩ := exists_extremal_of_target hK hS
  exact ⟨q, u, hq, hopt, hu, hmax, fun j hj => saw_eq_of_atom (fun r hr => (hS r hr).1) hq hopt hu hval hj⟩

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
