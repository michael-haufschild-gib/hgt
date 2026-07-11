import GaloisForLFunctions.GammaDifferentialFE

open Complex Filter Topology Finset Polynomial
open scoped BigOperators

namespace GaloisForLFunctions

/-- A pole of the expected derivative orders forces the leading ODE coefficient to vanish there. -/
theorem linear_top_isRoot_of_residue_at (f : ℂ → ℂ) (p : ℂ) (P : ℕ)
    (L : ℕ → ℂ) (hL : ∀ i, L i ≠ 0)
    (hres : ∀ i : ℕ, Tendsto (fun s : ℂ => (s - p) ^ (i + P) * iteratedDeriv i f s)
      (𝓝[≠] p) (𝓝 (L i)))
    (n : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, ∑ j ∈ range (n + 1), (c j).eval s * iteratedDeriv j f s = 0) :
    (c n).IsRoot p := by
  have h0 : Tendsto (fun s : ℂ => (s - p) ^ (n + P) *
      ∑ j ∈ range (n + 1), (c j).eval s * iteratedDeriv j f s)
      (𝓝[≠] p) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with s
    rw [hrel s]
    ring
  have hfun : (fun s : ℂ => (s - p) ^ (n + P) *
      ∑ j ∈ range (n + 1), (c j).eval s * iteratedDeriv j f s) =
      fun s : ℂ => ∑ j ∈ range (n + 1),
        (c j).eval s * ((s - p) ^ (n - j) *
          ((s - p) ^ (j + P) * iteratedDeriv j f s)) := by
    funext s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [mem_range, Nat.lt_succ_iff] at hj
    rw [← mul_assoc ((s - p) ^ (n - j)), ← pow_add,
      show (n - j) + (j + P) = n + P by omega]
    ring
  have hterms : Tendsto (fun s : ℂ => ∑ j ∈ range (n + 1),
      (c j).eval s * ((s - p) ^ (n - j) *
        ((s - p) ^ (j + P) * iteratedDeriv j f s)))
      (𝓝[≠] p)
      (𝓝 (∑ j ∈ range (n + 1),
        (c j).eval p * ((p - p) ^ (n - j) * L j))) := by
    apply tendsto_finsetSum
    intro j _
    have hcj : Tendsto (fun s : ℂ => (c j).eval s) (𝓝[≠] p) (𝓝 ((c j).eval p)) :=
      (c j).continuous.continuousAt.continuousWithinAt
    have hpow : Tendsto (fun s : ℂ => (s - p) ^ (n - j)) (𝓝[≠] p)
        (𝓝 ((p - p) ^ (n - j))) :=
      ((continuous_id.sub continuous_const).pow (n - j)).continuousAt.continuousWithinAt
    exact hcj.mul (hpow.mul (hres j))
  rw [hfun] at h0
  have hval : (∑ j ∈ range (n + 1),
      (c j).eval p * ((p - p) ^ (n - j) * L j)) = (c n).eval p * L n := by
    rw [Finset.sum_eq_single n]
    · rw [sub_self, Nat.sub_self, pow_zero, one_mul]
    · intro j hjmem hjn
      rw [mem_range, Nat.lt_succ_iff] at hjmem
      have hnj : n - j ≠ 0 := by omega
      rw [sub_self, zero_pow hnj, zero_mul, mul_zero]
    · intro h
      simp at h
  rw [hval] at hterms
  have hprod : (c n).eval p * L n = 0 := tendsto_nhds_unique hterms h0
  exact (mul_eq_zero.mp hprod).resolve_right (hL n)

/-- **Finite-pole coefficient-degree budget.** An order-`n` polynomial-coefficient linear ODE
whose leading coefficient is nonzero and whose solution has the expected pole tower at an injective
finite packet must spend at least one degree of that leading coefficient per pole. -/
theorem card_le_natDegree_linear_top_of_residue_packet {ι : Type*} [Fintype ι]
    (f : ℂ → ℂ) (p : ι → ℂ) (hp : Function.Injective p) (P : ℕ)
    (L : ℕ → ι → ℂ) (hL : ∀ i k, L i k ≠ 0)
    (hres : ∀ i k, Tendsto (fun s : ℂ => (s - p k) ^ (i + P) * iteratedDeriv i f s)
      (𝓝[≠] (p k)) (𝓝 (L i k)))
    (n : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, ∑ j ∈ range (n + 1), (c j).eval s * iteratedDeriv j f s = 0)
    (htop : c n ≠ 0) :
    Fintype.card ι ≤ (c n).natDegree := by
  classical
  let e : ι ↪ ℂ := ⟨p, hp⟩
  have hsubset : Finset.univ.map e ⊆ (c n).roots.toFinset := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨k, _, rfl⟩ := hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots htop]
    exact linear_top_isRoot_of_residue_at f (p k) P (fun i => L i k)
      (fun i => hL i k) (fun i => hres i k) n c hrel
  calc
    Fintype.card ι = (Finset.univ.map e).card := by rw [Finset.card_map, Finset.card_univ]
    _ ≤ (c n).roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ (c n).roots.card := Multiset.toFinset_card_le _
    _ ≤ (c n).natDegree := Polynomial.card_roots' _

/-- The coefficient-degree budget in intrinsic meromorphic language: a finite injective packet of
genuine simple poles consumes at least its cardinality in the leading ODE coefficient. -/
theorem card_le_natDegree_linear_top_of_meromorphic_simplePoles {ι : Type*} [Fintype ι]
    (f : ℂ → ℂ) (p : ι → ℂ) (hp : Function.Injective p)
    (hmero : ∀ k, MeromorphicAt f (p k))
    (horder : ∀ k, meromorphicOrderAt f (p k) = ((-1 : ℤ) : WithTop ℤ))
    (n : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, ∑ j ∈ range (n + 1), (c j).eval s * iteratedDeriv j f s = 0)
    (htop : c n ≠ 0) :
    Fintype.card ι ≤ (c n).natDegree := by
  classical
  have hext : ∀ k, ∃ (g : ℂ → ℂ) (ε : ℝ), 0 < ε ∧
      (∀ m : ℕ, ContDiffAt ℂ m g (p k)) ∧ g (p k) ≠ 0 ∧
      (Metric.ball (p k) ε \ {p k}) ⊆
        {z | f z = (z - p k)⁻¹ * g z ∧ g z ≠ 0 ∧ ∀ m : ℕ, ContDiffAt ℂ m g z} := by
    intro k
    obtain ⟨g, hg, hgne, hfacptd⟩ :=
      (meromorphicOrderAt_eq_int_iff (hmero k)).mp (horder k)
    have hfac' : f =ᶠ[𝓝[≠] (p k)] fun z => (z - p k)⁻¹ * g z := by
      filter_upwards [hfacptd] with z hz
      rw [hz]
      simp [zpow_neg, zpow_one]
    have hcomb : {z : ℂ | f z = (z - p k)⁻¹ * g z ∧ g z ≠ 0 ∧
        ∀ m : ℕ, ContDiffAt ℂ m g z} ∈ 𝓝[≠] (p k) := by
      filter_upwards [hfac', nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hgne),
        nhdsWithin_le_nhds hg.eventually_analyticAt] with z h1 h2 h3
      exact ⟨h1, h2, fun m => h3.contDiffAt⟩
    rw [Metric.mem_nhdsWithin_iff] at hcomb
    obtain ⟨ε, hε, hsub⟩ := hcomb
    refine ⟨g, ε, hε, fun m => hg.contDiffAt, hgne, fun z hz => hsub ⟨hz.1, ?_⟩⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hz.2 (by rw [Set.mem_singleton_iff]; exact h)
  choose g ε hε hGk hgval hsub using hext
  let U : ι → Set ℂ := fun k => Metric.ball (p k) (ε k) \ {p k}
  let L : ℕ → ι → ℂ := fun i k => g k (p k) * ((-1) ^ i * (i.factorial : ℂ))
  have hL : ∀ i k, L i k ≠ 0 := fun i k =>
    mul_ne_zero (hgval k)
      (mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero i))
  have hres : ∀ i k, Tendsto
      (fun s : ℂ => (s - p k) ^ (i + 1) * iteratedDeriv i f s)
      (𝓝[≠] (p k)) (𝓝 (L i k)) := by
    intro i k
    have key := iteratedDeriv_residue_of_factor_add f (g k) (-(p k)) (U k)
      (fun s hs h => hs.2 (by rw [Set.mem_singleton_iff]; linear_combination h))
      (by
        rw [neg_neg]
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Metric.ball_mem_nhds (p k) (hε k)), self_mem_nhdsWithin] with s hb hne
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
        exact ⟨hb, hne⟩)
      (fun s hs m => (hsub k hs).2.2 m)
      (by rw [neg_neg]; exact hGk k)
      (fun s hs => by
        refine Filter.eventuallyEq_of_mem
          ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hs) (fun t ht => ?_)
        show f t = g k t * (t + -(p k))⁻¹
        have hft := hsub k ht
        rw [hft.1, show t + -(p k) = t - p k by ring]
        ring)
      i
    rw [neg_neg] at key
    simpa only [L] using key.congr' (by
      filter_upwards with s
      rw [show s + -(p k) = s - p k by ring])
  exact card_le_natDegree_linear_top_of_residue_packet f p hp 1 L hL hres n c hrel htop

end GaloisForLFunctions
